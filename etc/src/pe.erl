-module(pe).
-export([parse_transform/2]).


parse_transform(Forms,_) ->
    [Function] = pp:getFns(Forms),
    try
        io:fwrite("Function = ~p~n",[Function]),
        reduce(Function,maps:new())
    of
        {Reduced,_}      -> io:fwrite("Reduced = ~p~n",[Reduced])
    catch
        error:Reason -> io:fwrite("Very bad error happened: ~p~n",[Reason])
    end,
    Forms.

reduce({function,L,Name,Args,Clauses},Env) ->
    Clauses_ = lists:map(fun(C)-> element(1,reduce(C,Env)) end, Clauses),
    {{function,L,Name,Args,Clauses_},Env};
reduce({clause,L,Patterns, Guards, Body},Env) ->
    {Body_,_} = lists:foldl(fun(B,{AccPs,AccEnv}) ->
        {B_,AccEnv_} = reduce(B,Env),
        {AccPs ++ [B_],AccEnv_}         
    end, {[],Env}, Body),
    {{clause,L,Patterns, Guards, Body_},Env};
reduce({op,L,Op,E1,E2},Env) -> 
    {E1_,_} = reduce(E1,Env),
    {E2_,_} = reduce(E2,Env),
    ReducedExpr = {op,L,Op,E1_,E2_},
    case isValue(E1_) and isValue(E2_) of
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

isValue({float,_,_})    -> true;
isValue({integer,_,_})  -> true;
isValue({atom,_,_})  -> true;
isValue({string,_,_})  -> true;
isValue(_)              -> false.

getMaxType(E1,E2) -> maxType(erl_syntax:type(E1),erl_syntax:type(E2)).

maxType(integer  ,integer)   -> integer;
maxType(integer  ,float)     -> float;
maxType(float    ,integer)   -> float;
maxType(float    ,float)     -> float;
maxType(T        ,T)         -> T.





