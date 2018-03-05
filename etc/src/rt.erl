-module(rt).
-export([defaultEnv/0,defaultClasses/0]).

-spec defaultClasses() -> [hm:predicate()].
defaultClasses() -> [
    {"Num",hm:bt(integer)},
    {"Num",hm:bt(float)},
    {"Fractional",hm:bt(float)}
].

-spec defaultEnv() -> hm:env().
defaultEnv() ->
    lists:foldl(fun({X,T},Env) -> env:extend(X,T,Env) end, env:empty(), [
        {'+', hm:forall(a,[{"Num", hm:tvar(a)}],
                hm:funt([hm:tvar(a),hm:tvar(a)],hm:tvar(a))) },
        {'div', hm:funt([hm:bt(integer),hm:bt(integer)],hm:bt(integer))}
    ]).
