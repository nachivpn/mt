-module(rt).
-export([defaultEnv/0,defaultClasses/0]).

-spec defaultClasses() -> [hm:predicate()].
defaultClasses() -> [
    {"Num",hm:bt(integer,0)},
    {"Num",hm:bt(float,0)}
].

-spec defaultEnv() -> hm:env().
defaultEnv() ->
    lists:foldl(fun({X,T},Env) -> env:extend(X,T,Env) end, env:empty(), [
        {'+', hm:forall(a,[{"Num", hm:tvar(a,0)}],
                hm:funt([hm:tvar(a,0),hm:tvar(a,0)],hm:tvar(a,0),0),0) },
        {'-', hm:forall(a,[{"Num", hm:tvar(a,0)}],
                hm:funt([hm:tvar(a,0),hm:tvar(a,0)],hm:tvar(a,0),0),0) },
        {'div', hm:funt([hm:bt(integer,-1),hm:bt(integer,-2)],hm:bt(integer,-3),0)}
    ]).
