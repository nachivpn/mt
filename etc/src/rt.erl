-module(rt).
-export([defaultEnv/0]).

-spec defaultEnv() -> hm:env().
defaultEnv() ->
    lists:foldl(fun({X,T},Env) -> env:extend(X,T,Env) end, env:empty(), [
        {'+', hm:forall(a,[{"Num", hm:tvar(a)}],hm:funt([hm:tvar(a),hm:tvar(a)],hm:tvar(a))) }
    ]).
