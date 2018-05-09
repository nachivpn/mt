-module(pe).
-export([parse_transform/2]).


parse_transform(Forms,_) ->
    [Function] = pp:getFns(Forms),
    io:fwrite("Function = ~p~n",[Function]),
    {Reduced,_} = reduce(Function,maps:new()),
    io:fwrite("Reduced = ~p~n",[Reduced]),
    lists:sublist(Forms,3) ++ [Reduced] ++ lists:nthtail(4,Forms).

reduce({function,L,Name,Args,Clauses},Env) ->
    Clauses_ = lists:map(fun(C)-> element(1,reduce(C,Env)) end, Clauses),
    {{function,L,Name,Args,Clauses_},Env};
reduce({clause,L,Patterns, Guards, Body},Env) ->
    {Body1,_} = lists:foldl(fun(B,{AccPs,AccEnv}) ->
        {B_,AccEnv_} = reduce(B,AccEnv),
        {AccPs ++ [B_],AccEnv_}   
    end, {[],Env}, Body),
    Body2 = elimDeadBody(Body1),
    {{clause,L,Patterns, Guards, Body2},Env};
reduce({'if',L,Clauses},Env) ->
    {_,Clauses_} = lists:foldl(
    fun({clause,CL,Patterns,Guards,Body},{BranchFound,AccCs}) ->
        if
            % branch taken already, don't reduce further
            BranchFound     -> {BranchFound,AccCs};
            % branch not taken, reduce!
            true            ->
                Guards_ = reduceGuards(Guards,Env),
                case Guards_ of
                    % this branch evaluted to true, discard previous branches
                    [[{atom,_,true}]]   -> {true,[{clause,CL,Patterns,Guards_,Body}]};
                    % this branch evaluted to false, discard it
                    [[{atom,_,false}]]  -> {false,AccCs};
                    % this branch didn't evaluate to a value, accumulate reduced form
                    _                   -> {false,AccCs ++ [{clause,CL,Patterns,Guards_,Body}]}
                end
        end
    end ,{false,[]}, Clauses),
    {{'if',L,Clauses_},Env};
reduce({match,L,LExpr,RExpr},Env) ->
    {LExpr_,Env1} = reduce(LExpr,Env),
    {RExpr_,Env2} = reduce(RExpr,Env1),
    Sub = unify(LExpr_,RExpr_), 
    Env3 = maps:merge(Env2,Sub),
    case isStatic(RExpr_) of
        true    -> {RExpr_,Env3};
        false   -> {{match,L,LExpr_,RExpr_},Env3}
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
    {E1_,_} = reduce(E1,Env),
    {E2_,_} = reduce(E2,Env),
    ReducedExpr = {op,L,Op,E1_,E2_},
    case isStatic(E1_) and isStatic(E2_) of
        true        -> 
            {value,V,_} = erl_eval:expr(ReducedExpr,[]),
            {{getMaxType(E1_,E2_),L,V}, Env};
        false       -> 
            {ReducedExpr, Env}
    end;
reduce({op,L,Op,E},Env) -> 
    {E_,_} = reduce(E,Env),
    ReducedExpr = {op,L,Op,E_},
    case isStatic(E_)of
        true        -> 
            {value,V,_} = erl_eval:expr(ReducedExpr,[]),
            {{erl_syntax:type(E_),L,V}, Env};
        false       -> 
            {ReducedExpr, Env}
    end;
reduce(E={var,_,X},Env)     -> {maps:get(X,Env,E),Env};
reduce(E={float,_,_},Env)   -> {E, Env};
reduce(E={integer,_,_},Env) -> {E, Env};
reduce(E={string,_,_},Env)  -> {E, Env};
reduce(E={atom,_,_},Env)    -> {E, Env}.


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
isStatic({tuple,_,Es})  -> lists:all(fun isStatic/1,Es).

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

elimDeadBody(Body) ->
    lists:filter(
        fun (B) -> not isStatic(B) end, 
        lists:droplast(Body)) 
    ++ [lists:last(Body)].
