-module(pe).
-export([parse_transform/2]).


parse_transform(Forms,_) ->
    [Function] = pp:getFns(Forms),
    Reduced = reduceTopFn(Function),
    lists:sublist(Forms,3) ++ [Reduced] ++ lists:nthtail(4,Forms).

reduceTopFn({function,L,Name,Args,Clauses}) ->
    Clauses_ = lists:map(
        fun(C)-> reduceTopFunClause(C,maps:new()) end, Clauses),
    {function,L,Name,Args,Clauses_}.

reduceTopFunClause({clause,L,Patterns, Guards, Body},Env) ->
    {Body_,_} = reduceClauseBody(Body,Env),
    {clause,L,Patterns, Guards, Body_}.

reduce({'if',L,Clauses},Env) ->
    Clauses_ = reduceClauses(Clauses,Env),
    case Clauses_ of
        [{clause,_,_,[[{atom,_,true}]],[Expr_]}] -> {Expr_,Env};
        _         -> {{'if',L,Clauses_},Env}
    end;
reduce({match,L,LExpr,RExpr},Env) ->
    {LExpr_,Env1} = reduce(LExpr,Env),
    {RExpr_,Env2} = reduce(RExpr,Env1),
    Sub = unify(LExpr_,RExpr_), 
    Env3 = maps:merge(Env2,Sub),
    % this is important to preserve call by value semantics
    case isValue(RExpr_) of
        % since the RHS is a value, 
        % we return the value (which may or may not be used upstream)
        % it is safe to return the new env (containing substitution)
        true    -> {RExpr_,Env3};
        % the RHS is not a value, we must simply 
        % return the old env and reduced match expr (because it is simpler)
        % new env is "unsafe" cz it contains
        % substitution with non-value exprs (i.e., possibly effectful)
        false   -> {{match,L,LExpr_,RExpr_},Env}
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
            {value,V,_} = erl_eval:expr(ReducedExpr,[]),
            {{getMaxType(E1_,E2_),L,V}, Env2};
        false       -> 
            {ReducedExpr, Env2}
    end;
reduce({op,L,Op,E},Env) -> 
    {E_,Env_} = reduce(E,Env),
    ReducedExpr = {op,L,Op,E_},
    case isStatic(E_)of
        true        -> 
            {value,V,_} = erl_eval:expr(ReducedExpr,[]),
            {{erl_syntax:type(E_),L,V}, Env_};
        false       -> 
            {ReducedExpr, Env_}
    end;
reduce(E={var,_,X},Env)     -> {maps:get(X,Env,E),Env};
reduce(E={float,_,_},Env)   -> {E, Env};
reduce(E={integer,_,_},Env) -> {E, Env};
reduce(E={string,_,_},Env)  -> {E, Env};
reduce(E={atom,_,_},Env)    -> {E, Env}.


reduceClause({clause,CL,Patterns,Guards,Body},Env) ->
    Guards_  = reduceGuards(Guards,Env),
    {Body_,_} = reduceClauseBody(Body,Env),
    {{clause,CL,Patterns,Guards_,Body_},Env}.

reduceClauses(Clauses,Env) ->
    Clauses1 = lists:map(fun(C) -> element(1,reduceClause(C,Env))end,Clauses),
    IsTrueGuard = fun({clause,_,_,Guards,_}) -> 
        case Guards of [[{atom,_,X}]]  -> X;
                        _               -> false
        end end,
    IsDynamicGuard = fun({clause,_,_,Guards,_}) -> 
        case Guards of  [[{atom,_,_}]]  -> false;
                        _               -> true
        end end,
    % remove false clauses
    Clauses2 = lists:filter(fun(C) -> IsTrueGuard(C) or IsDynamicGuard(C) end, Clauses1),
    % take the first true clause
    {_,Clauses3} = lists:foldl(fun(C,{BranchFound,AccCs}=Acc) ->
        case BranchFound of
            true -> Acc;
            false ->
                case length(AccCs) == 0 andalso IsTrueGuard(C) of
                    true ->     {true,[C]};
                    false ->    {false,AccCs ++ [C]}
                end
        end
    end,{false,[]},Clauses2),
    Clauses3.

reduceClauseBody(Body,Env) ->
    {Body1,_} = lists:foldl(fun(B,{AccPs,AccEnv}) ->
        {B_,AccEnv_} = reduce(B,AccEnv),
        {AccPs ++ [B_],AccEnv_}
    end, {[],Env}, Body),
    Body2 = elimDeadBody(Body1),
    {Body2,Env}.

reduceGuards(Disjunctions,Env) ->
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
   StaticDisjunctions = lists:all(
        fun(D) -> length(D) == 1 
            andalso isStatic(lists:nth(1,D)) 
        end, Disjunctions_),
   case StaticDisjunctions of    
            true    -> 
                Value = lists:any(fun(D) -> getValue(lists:nth(1,D)) end, Disjunctions_),
                L = util:getLn(lists:nth(1,lists:nth(1,Disjunctions_))),
                [[{atom,L,Value}]];
            false   -> Disjunctions_
    end.


isStatic({float,_,_})   -> true;
isStatic({integer,_,_}) -> true;
isStatic({atom,_,_})    -> true;
isStatic({string,_,_})  -> true;
isStatic({nil,_})       -> true;
isStatic({var,_,_})     -> false;
isStatic({match,_,_,R}) -> isStatic(R);
isStatic({cons,_,H,T})  -> isStatic(H) and isStatic(T);
isStatic({tuple,_,Es})  -> lists:all(fun isStatic/1,Es);
isStatic(_)  -> false.


getValue(V) -> element(3,V).


getMaxType(E1,E2) -> maxType(erl_syntax:type(E1),erl_syntax:type(E2)).

maxType(integer  ,integer)   -> integer;
maxType(integer  ,float)     -> float;
maxType(float    ,integer)   -> float;
maxType(float    ,float)     -> float;
maxType(T        ,T)         -> T.

unify({cons,_,LH,LT},{cons,_,RH,RT}) -> 
    Sub1 = unify(LH,RH),
    LT_ = applySub(Sub1,LT),
    RT_ = applySub(Sub1,RT),
    Sub2 = unify(LT_,RT_),
    comp(Sub2,Sub1);
unify({tuple,_,Es1},{tuple,_,Es2})   -> 
    case length(Es1) == length(Es2) of
        false -> erlang:error({pe_error,"Cannot unify tuples"});
        true -> 
            lists:foldl(fun({E1,E2},AccSub) ->
                S = unify(applySub(AccSub,E1),applySub(AccSub,E2)),
                comp(S,AccSub)
            end, maps:new(), lists:zip(Es1,Es2))
    end;
unify({var,_,X},R)                  -> maps:put(X,R,maps:new());
% TODO what if variable on R is not defined
unify(L,R={var,_,_})                -> unify(R,L);
unify({nil,_},{nil,_})              -> maps:new();
unify({integer,_,I},{integer,_,I})  -> maps:new();
unify(_,_)                          ->
    erlang:error({pe_error,"Cannot unify patterns!"}).


applySub(Sub,{cons,L,H,T}) -> {cons,L,applySub(Sub,H),applySub(Sub,T)};
applySub(Sub,{var,L,X}) -> maps:get(X,Sub,{var,L,X});
applySub(_,E) -> E.

comp (X,Y) ->
    Y_ = maps:map( % apply subtitution X on every entry in Y
            fun(_,Type) -> applySub(X,Type) end, Y),
    maps:merge(X,Y_).   % union (Y_, entries in X whose keys are not in Y)

isValue({float,_,_})    -> true;
isValue({integer,_,_})  -> true;
isValue({atom,_,_})     -> true;
isValue({string,_,_})   -> true;
isValue({nil,_})        -> true;
isValue({var,_,_})      -> true;
isValue({cons,_,_,_})   -> true;
isValue({tuple,_,_})    -> true;
isValue({op,_,_,E})    -> isValue(E);
isValue({op,_,_,E1,E2}) -> isValue(E1) and isValue(E2);
isValue(_) -> false.

elimDeadBody(Body) ->
    lists:filter(
        fun (B) -> not isValue(B) end, 
        lists:droplast(Body)) 
    ++ [lists:last(Body)].
