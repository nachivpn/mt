-module(rt).
-export([defaultEnv/0]).

-spec defaultEnv() -> hm:env().
defaultEnv() ->
    lists:foldl(fun({X,T},Env) -> env:extend(X,T,Env) end, env:empty(), [
        {'+', hm:funt([hm:bt(integer),hm:bt(integer)],hm:bt(integer))}
    ]).
