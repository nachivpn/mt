-module(pe).
-export([parse_transform/2]).


parse_transform(Forms,_) ->
    [Function] = pp:getFns(Forms),
    io:fwrite("Function = ~p~n",[Function]),
    {Reduced,_} = reduce(Function,maps:new()),
    io:fwrite("Reduced = ~p~n",[Reduced]),
   Forms.

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
reduce(E={var,_,X},Env)     -> {maps:get(X,Env,E),Env};
reduce(E={float,_,_},Env)   -> {E, Env};
reduce(E={integer,_,_},Env) -> {E, Env};
reduce(E={string,_,_},Env)  -> {E, Env};
reduce(E={atom,_,_},Env)    -> {E, Env}.

isStatic({float,_,_})   -> true;
isStatic({integer,_,_}) -> true;
isStatic({atom,_,_})    -> true;
isStatic({string,_,_})  -> true;
isStatic({nil,_})       -> true;
isStatic({var,_,_})     -> false;
isStatic({match,_,_,R}) -> isStatic(R);
isStatic({cons,_,H,T})  -> isStatic(H) and isStatic(T);
isStatic({tuple,_,Es})  -> lists:all(fun isStatic/1,Es).

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


% unify(L,R) -> io:fwrite("L = ~p~nR = ~p",[L,R]).

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
