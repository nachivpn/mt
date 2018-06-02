-module(pe).
-export([parse_transform/2]).
-include_lib("erlscp/src/scp.hrl").

% Partial evaluation ENvironment
-record(pen, 
    {   vars    %map of variable => value
    ,   funs    %map of {funName,Arity} => FunctionNode
    ,   bound
    }).

parse_transform(Forms,_) ->
    FunEnv = lists:foldl(fun(F,Map) ->
        case F of
            {function,_,Name,ArgLen,_} ->
                % convert top level function to fun value
                Fun = scp_expr:function_to_fun(F), 
                maps:put({Name,ArgLen},Fun,Map) ;
            _   -> Map
        end
    end, maps:new(), Forms),
    pp:fmapPEFns(fun(Function) -> 
        reduceTopFn(Function,#pen{vars = maps:new(),funs = FunEnv})
    end, Forms).

reduceTopFn({function,L,Name,Args,Clauses},Env) ->
    Clauses_ = lists:map(
        fun(C)-> reduceTopFunClause(C,Env) end, Clauses),
    {function,L,Name,Args,Clauses_}.

reduceTopFunClause({clause,L,Patterns, Guards, Body},Env) ->
    BoundArgVars = lists:foldr(fun(P,AccSet) ->
        sets:union(AccSet,erl_syntax_lib:variables(P))
    end,sets:new(), Patterns), 
    Body_ = reduceClauseBody(Body,Env#pen{bound = BoundArgVars}),
    {clause,L,Patterns, Guards, Body_}.
    
reduce({call,L,{atom,L,FunName},Args},Env) ->
    % reduce all the arguments
    Args_ = lists:map(fun(A) -> element(1,reduce(A,Env)) end,Args),
    Call_ = {call,L,{atom,L,FunName},Args_},
    case lists:all(fun isStatic/1,Args_) of
        % then, inline
        true ->
            try
                FnKey = {FunName,length(Args_)},
                StaticArgs = lists:all(fun isStatic/1,Args_),
                case {maps:is_key(FnKey,Env#pen.funs),StaticArgs} of
                    % function body is available in environment
                    {true,_}    ->
                        % get called function body
                        Fun = maps:get(FnKey,Env#pen.funs),
                        % rename variables
                        {_,{'fun',LF,{clauses,Clauses}}} = scp_expr:alpha_convert(#env{},Fun),
                        % filter matching clauses
                        Clauses_ = filterClauses(Clauses,Args_,Env),
                        ReducedFun = {call,L,{'fun',LF,{clauses,Clauses_}},Args_},
                        {decideClause(Clauses_,L,ReducedFun),Env};
                    % since function body is not available, 
                    % it's probably a default function
                    % arguments are static, so call meta-interpreter erl_eval
                    {_,true}   ->
                        {value,V,_} = erl_eval:expr(Call_,[]),
                        {mkNode(V,L), Env};
                    {_,false}  ->
                        {Call_,Env}
                end
            catch
                error:{pe_error,no_match, Reason} ->
                    erlang:error("When evaluating function call on line " 
                    ++ util:to_string(L) ++ ", no_match occured: " ++ Reason)
            end;
        % else, leave call as it is
        false ->
            {Call_,Env}
    end;
reduce({'case',L,MainExpr,Clauses},Env) ->
    {MainExpr_,_}   = reduce(MainExpr,Env),
    % reduce clauses to static values for elimination
    Clauses1        = lists:map(fun(C) -> reduceClause(C,Env) end, Clauses),
    % eliminate branches known to be dead
    Clauses2        = filterClauses(Clauses1,[MainExpr_],Env),
    ReducedCase     = {'case',L,MainExpr_,Clauses2},
    {decideClause(Clauses2,L,ReducedCase),Env};
reduce({'if',L,Clauses},Env) ->
    % reduce clauses to static values for elimination
    Clauses1    = lists:map(fun(C) -> reduceClause(C,Env) end, Clauses),
    % eliminate branches known to be dead
    Clauses2    = filterClauses(Clauses1,[],Env),
    ReducedIf   = {'if',L,Clauses2}, 
    {decideClause(Clauses2,L,ReducedIf),Env};
reduce({match,L,LExpr,RExpr},Env) ->
    {LExpr_,Env1} = reduce(LExpr,Env),
    % add all variables on left expr to bound (seen)
    Env1_       = Env1#pen{bound=sets:union(Env1#pen.bound,erl_syntax_lib:variables(LExpr_))},
    {RExpr_,_}  = reduce(RExpr,Env),
    {Sub,Ds}    = unify(LExpr_,RExpr_),
    Env2        = addSubToEnv(Sub,Env1_,L),
    Matches     = scopeNewVarsIn(Sub,Env,L) ++ dynamicSubsAsMatches(Ds,L),
    case Matches of
        []  -> {RExpr_,Env2};
        [M] -> {M,Env2};
        _   -> {{block,L,Matches},Env2}
    end;
reduce({cons,L,HExpr,TExpr},Env) ->
    {HExpr_,Env1} = reduce(HExpr,Env),
    {TExpr_,Env2} = reduce(TExpr,Env1),
    {{cons,L,HExpr_,TExpr_},Env2};
reduce({nil,L},Env) ->
    {{nil,L},Env};
reduce({tuple,L,Es},Env) ->
    {Es_,Env_} = lists:foldl(fun(E,{AccEs,AccEnv}) ->
        {E_,AccEnv_} = reduce(E,AccEnv),
        {AccEs ++ [E_],AccEnv_}
    end,{[],Env}, Es),
    {{tuple,L,Es_},Env_};
reduce({op,L,Op,E1,E2},Env) -> 
    {E1_,Env1} = reduce(E1,Env),
    {E2_,Env2} = reduce(E2,Env1),
    ReducedExpr = {op,L,Op,E1_,E2_},
    case isStatic(E1_) and isStatic(E2_) of
        true        -> 
            try
                erl_eval:expr(ReducedExpr,[])
            of
                {value,V,_} -> {{getMaxType(E1_,E2_),L,V}, Env2}
            catch
                error:_ -> {ReducedExpr, Env2}
            end;
        false       -> 
            {ReducedExpr, Env2}
    end;
reduce({op,L,Op,E},Env) -> 
    {E_,Env_} = reduce(E,Env),
    ReducedExpr = {op,L,Op,E_},
    case isStatic(E_)of
        true        -> 
            try
                erl_eval:expr(ReducedExpr,[])
            of
                {value,V,_} -> {{erl_syntax:type(E_),L,V}, Env_}
            catch
                error:_ -> {ReducedExpr, Env_}
            end;
        false       -> 
            {ReducedExpr, Env_}
    end;
reduce(E={var,_,X},Env)     -> {maps:get(X,Env#pen.vars,E),Env};
reduce(E={float,_,_},Env)   -> {E, Env};
reduce(E={integer,_,_},Env) -> {E, Env};
reduce(E={string,_,_},Env)  -> {E, Env};
reduce(E={atom,_,_},Env)    -> {E, Env};
% HACK! doesn't reduce unhandled expr
reduce(E,Env)               -> {E, Env}.


reduceClause({clause,CL,Patterns,Guards,Body},Env) ->
    Patterns_ = reduceClausePatterns(Patterns,Env),
    BoundPatVars = lists:foldr(fun(P,AccSet) ->
                sets:union(AccSet,erl_syntax_lib:variables(P))
            end,sets:new(), Patterns), 
    Env_    = Env#pen{bound = sets:union(Env#pen.bound,BoundPatVars)},
    Guards_ = reduceClauseGuards(Guards,Env),
    Body_   = reduceClauseBody(Body,Env_),
    {clause,CL,Patterns_,Guards_,Body_}.

reduceClauseBody(Body,Env) ->
    {Body1,_} = lists:foldl(fun(B,{AccPs,AccEnv}) ->
        {B_,AccEnv_} = reduce(B,AccEnv),
        {AccPs ++ [B_],AccEnv_}
    end, {[],Env}, Body),
    elimDeadBody(Body1).

reduceClausePatterns(Patterns,Env) ->
    lists:foldl(fun(P,AccPs) ->
        {P_,_} = reduce(P,Env),
        AccPs ++ [P_]
    end, [], Patterns).

reduceClauseGuards(Disjunctions,Env) ->
    Disjunctions_ = lists:foldr(fun(Conjunctions, DAccExprs) ->
        Conjunctions_ = lists:foldr(fun(Expr,CAccExprs) ->
            {Expr_,_} = reduce(Expr,Env),
            [Expr_|CAccExprs]
        end, [], Conjunctions),
        case lists:all(fun isStatic/1,Conjunctions_) of    
            true    -> 
                Value = lists:all(fun getValue/1,Conjunctions_),
                L = util:getLn(lists:nth(1,Conjunctions_)),
                [[{atom,L,Value}]|DAccExprs];
            false   -> [Conjunctions_|DAccExprs]
        end
   end, [], Disjunctions),
   StaticDisjunctions = length(Disjunctions_) > 0 
        andalso lists:all(fun(D) -> length(D) == 1 
                    andalso isStatic(lists:nth(1,D)) 
                end, Disjunctions_),
   case StaticDisjunctions of    
            true    -> 
                Value = lists:any(fun(D) -> getValue(lists:nth(1,D)) end, Disjunctions_),
                L = util:getLn(lists:nth(1,lists:nth(1,Disjunctions_))),
                [[{atom,L,Value}]];
            false   -> Disjunctions_
    end.

filterClauses([],_,_)         -> [];
filterClauses([{clause,L,Patterns,_,_}=C|Cs],Args,Env) ->
    try 
        % unify to obtain susbtitution for pattern 
        % in terms of main expr (order matters!)
        unifyMany(Patterns,Args)
    of
        {Sub,Ds} ->
            BoundPatVars = lists:foldr(fun(P,AccSet) ->
                sets:union(AccSet,erl_syntax_lib:variables(P))
            end,sets:new(), Patterns), 
            % reduce the clause in a new env w/ sub only (to avoid interference)
            ReductionEnv    = #pen{vars = maps:new(),bound = sets:union(Env#pen.bound,BoundPatVars)},
            ReductionEnv_   = addSubToEnv(Sub,ReductionEnv,L),
            C1              = reduceClause(C,ReductionEnv_),
            {clause,L,Patterns_,Guards_,Body_} = C1,
            % bind new variables in patterns & get dynamic subs as matches
            BindingMatches = scopeNewVarsIn(Sub,Env,L) ++ dynamicSubsAsMatches(Ds,L),
            C2 = {clause,L,Patterns_,Guards_, BindingMatches ++ Body_},
            % checks used for clause matching
            PAs = lists:zip(Patterns_,Args),
            Static = lists:all(fun({P,A})-> isStatic(P) and isStatic(A) end,PAs),
            Matches = lists:all(fun({P,A}) -> matches(P,A) end,PAs),
            case {Static,Matches,Guards_} of
                % cannot determine pattern match at compile time
                {false,_,_}                     -> [C2] ++ filterClauses(Cs,Args,Env);
                % static values but still pattern matching fails, discard
                {true,false,_}                  -> filterClauses(Cs,Args,Env);
                % guard evaluates to false, discard
                {true,_,[[{atom,_,false}]]}     -> filterClauses(Cs,Args,Env);
                % pattern matches (no guards), take it and keep only this!
                {true,true,[]}                  -> [C2];
                % pattern matches and guard evaluates to true, keep only this!
                {true,true,[[{atom,_,true}]]}   -> [C2]
            end
    catch
        error:{pe_error,unification,_} -> 
            filterClauses(Cs,Args,Env)
    end.

% given a list of reduced clauses,
% if only one matching clause is available, return its body
% else, return the 3rd argument (ReducedExpr)
decideClause(Clauses,L,ReducedExpr) ->
    case Clauses of
        []  -> erlang:error({pe_error,no_match, "No matching clause on line " ++ util:to_string(L)});
        % only one branch is left, take it! (singl expr body)
        [{clause,_,_,[[{atom,_,true}]],[Expr_]}]    -> Expr_;
        [{clause,_,_,[],[Expr_]}]                   -> Expr_;
        % only one branch is left, take it! (multiple expr body)
        [{clause,_,_,[[{atom,_,true}]],Exprs_}]     -> {block,L,Exprs_};
        [{clause,_,_,[],Exprs_}]                    -> {block,L,Exprs_};
        % more than one branch is left, return reduced expr
        _                                           -> ReducedExpr
    end.


%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Pattern matching
%%%%%%%%%%%%%%%%%%%%%%%% 

% unify two patterns
unify({cons,_,LH,LT},{cons,_,RH,RT}) -> 
    {Sub1,Ds1} = unify(LH,RH),
    LT_ = applySub(Sub1,LT),
    RT_ = applySub(Sub1,RT),
    {Sub2,Ds2} = unify(LT_,RT_),
    {comp(Sub2,Sub1),Ds1++Ds2};
unify({tuple,_,Es1},{tuple,_,Es2})   -> 
    case length(Es1) == length(Es2) of
        false -> erlang:error({pe_error,unification,"Cannot unify tuples"});
        true -> 
            lists:foldl(fun({E1,E2},{AccSub,AccDs}) ->
                {S,Ds} = unify(applySub(AccSub,E1),applySub(AccSub,E2)),
                {comp(S,AccSub),AccDs ++ Ds}
            end, {maps:new(),[]}, lists:zip(Es1,Es2))
    end;
unify({var,_,X},{var,_,X})          -> {maps:new(),[]};
unify({var,_,X},R)                  ->
    case {occurs(X,R),isValue(R)} of
        {true,_}        -> 
            erlang:error({pe_error,unification,"occurs check!"});
        {false,true}    -> 
            {maps:put(X,R,maps:new()),[]};
        {false,false}   -> 
            {maps:new(),[{X,R}]}
    end;
% TODO what if variable on R is not defined
unify(L,R={var,_,_})                -> unify(R,L);
unify({nil,_},{nil,_})              -> {maps:new(),[]};
unify({integer,_,I},{integer,_,I})  -> {maps:new(),[]};
unify({atom,_,A},{atom,_,A})        -> {maps:new(),[]};
unify({string,_,S},{string,_,S})    -> {maps:new(),[]};
unify({float,_,F},{float,_,F})      -> {maps:new(),[]};
unify(X,Y)                          ->
    erlang:error({pe_error,unification,"Cannot unify patterns: " 
    ++ util:to_string(X) ++ " and " ++ util:to_string(Y)}).

unifyMany([],[])            -> {maps:new(),[]};
unifyMany([],_)             -> erlang:error({pe_error, unification, "arg_mismatch"});
unifyMany(_,[])             -> erlang:error({pe_error, unification, "arg_mismatch"});
unifyMany ([A0|As],[B0|Bs])   ->
    {Sub0,Ds0} = unify(A0,B0),
    As_ = lists:map(fun(A1) -> applySub(Sub0,A1) end, As),
    Bs_ = lists:map(fun(B1) -> applySub(Sub0,B1) end, Bs),
    {Sub,Ds} = unifyMany(As_,Bs_),
    {comp(Sub,Sub0),Ds0 ++ Ds}.

applySub(Sub,{cons,L,H,T}) -> {cons,L,applySub(Sub,H),applySub(Sub,T)};
applySub(Sub,{var,L,X}) -> maps:get(X,Sub,{var,L,X});
applySub(_,E) -> E.

comp (X,Y) ->
    Y_ = maps:map( % apply subtitution X on every entry in Y
            fun(_,Type) -> applySub(X,Type) end, Y),
    maps:merge(X,Y_).   % union (Y_, entries in X whose keys are not in Y)

% Do the given patterns match during specialization time?
matches({cons,_,LH,LT},{cons,_,RH,RT}) -> 
    matches(LH,RH) and matches(LT,RT);
matches({tuple,_,Es1},{tuple,_,Es2})   -> 
    length(Es1) == length(Es2) 
        andalso
    lists:all(
        fun({E1,E2}) -> matches(E1,E2) end,lists:zip(Es1,Es2));
matches({var,_,X},{var,_,X})            -> true;
matches({nil,_},{nil,_})                -> true;
matches({integer,_,I},{integer,_,I})    -> true;
matches({atom,_,A},{atom,_,A})          -> true;
matches({string,_,S},{string,_,S})      -> true;
matches({float,_,F},{float,_,F})        -> true;
matches(_,_)                            -> false.


occurs(X,{cons,_,H,T})  -> occurs(X,H) or occurs(X,T);
occurs(X,{tuple,_,Es})  -> lists:any(fun(E) -> occurs(X,E) end, Es);
occurs(X,{var,_,X})     -> true;
occurs(_,_)             -> false.

%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Utilities
%%%%%%%%%%%%%%%%%%%%%%%% 

% is the given node a known (static) value?
isStatic({float,_,_})   -> true;
isStatic({integer,_,_}) -> true;
isStatic({atom,_,_})    -> true;
isStatic({string,_,_})  -> true;
isStatic({nil,_})       -> true;
isStatic({var,_,_})     -> false;
isStatic({cons,_,H,T})  -> isStatic(H) and isStatic(T);
isStatic({tuple,_,Es})  -> lists:all(fun isStatic/1,Es);
isStatic(_)  -> false.

% is the given node a (static or dynamic) value?
isValue({float,_,_})    -> true;
isValue({integer,_,_})  -> true;
isValue({atom,_,_})     -> true;
isValue({string,_,_})   -> true;
isValue({nil,_})        -> true;
isValue({var,_,_})      -> true;
isValue({cons,_,H,T})   -> isValue(H) and isValue(T); 
isValue({tuple,_,Es})   -> lists:all(fun isValue/1, Es);
isValue(_) -> false.

getValue(V) -> element(3,V).

getMaxType(E1,E2) -> maxType(erl_syntax:type(E1),erl_syntax:type(E2)).

maxType(integer  ,integer)   -> integer;
maxType(integer  ,float)     -> float;
maxType(float    ,integer)   -> float;
maxType(float    ,float)     -> float;
maxType(T        ,T)         -> T.

mkNode(X,L) when is_integer(X) -> {integer,L,X};
mkNode(X,L) when is_float(X) -> {float,L,X};
mkNode(X,L) when is_atom(X) -> {atom,L,X};
mkNode(X,L) when is_tuple(X) -> 
    {tuple,L,lists:map(fun(E) ->mkNode(E,L) end,tuple_to_list(X))}.

% eliminate dangling values in a expression (list) body
elimDeadBody(Body) ->
    lists:filter(
        fun (B) -> not isValue(B) end, 
        lists:droplast(Body)) 
    ++ [lists:last(Body)].

dynamicSubsAsMatches(Ds,L) ->
    lists:foldl(fun({X,BoundExpr},AccMatches) ->
            AccMatches ++ [{match,L,{var,L,X},BoundExpr}]
        end, [], Ds).

addSubToEnv(Sub,Env,L) ->
    UnBoundVars = lists:filter(
        fun(Var) -> not sets:is_element(Var,Env#pen.bound) end
    , maps:keys(Sub)),
    case UnBoundVars of
        []      -> ok;
        ['_']   -> ok;
        _  -> 
            erlang:error({pe_error,unbound_var,
                "Unbound variable on line " ++ util:to_string(L) ++ ": " ++ util:to_string(UnBoundVars)})
    end,  
    Env#pen{vars=comp(Sub,Env#pen.vars)}.


unboundVars(Node,Env) ->
    sets:subtract(erl_syntax_lib:variables(Node),Env#pen.bound).

% If there are any unbound variables in the subtitution
% then, we must create a match expression to avoid unbound var scope
scopeNewVarsIn(Sub,Env,L) ->
    lists:foldl(fun({X,Expr},AccMatches) ->
        UnboundVars = unboundVars(Expr,Env),
        case sets:size(UnboundVars) > 0 of
            true -> [{match,L,Expr,{var,L,X}}|AccMatches];
            false -> AccMatches
        end
    end, [], maps:to_list(Sub)).