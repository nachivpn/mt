-module(rt).
-export([defaultEnv/0,defaultClasses/0]).

-spec defaultClasses() -> [hm:predicate()].
defaultClasses() -> [
    {class,"Num",hm:bt(integer,0)},
    {class,"Num",hm:bt(float,0)},
    {class,"Pid",hm:bt(pid,0)},
    {class,"Pid",hm:bt(atom,0)},
    {class,"Pid",hm:tcon("Tuple",[hm:bt(atom,0),hm:bt(atom,0)],0)} 
].

-spec defaultEnv() -> hm:env().
defaultEnv() ->
    lists:foldl(fun({X,T},Env) -> env:extend(X,T,Env) end, env:empty(), [
        {'+', hm:forall(a,[{class,"Num", hm:tvar(a,0)}],
                hm:funt([hm:tvar(a,-1),hm:tvar(a,-2)],hm:tvar(a,0),0),0) },
        {'-', hm:forall(a,[{class,"Num", hm:tvar(a,0)}],
                hm:funt([hm:tvar(a,-1),hm:tvar(a,-2)],hm:tvar(a,0),0),0) },
        {'*', hm:forall(a,[{class,"Num", hm:tvar(a,0)}],
                hm:funt([hm:tvar(a,-1),hm:tvar(a,-2)],hm:tvar(a,0),0),0) },
        {'/', hm:forall(a,[{class,"Num", hm:tvar(a,0)}],
                hm:funt([hm:tvar(a,-1),hm:tvar(a,-2)],hm:tvar(a,0),0),0) },
        {'div', hm:funt([hm:bt(integer,-1),hm:bt(integer,-2)],hm:bt(integer,0),0)},
        {'rem', hm:funt([hm:bt(integer,-1),hm:bt(integer,-2)],hm:bt(integer,0),0)},
        {'band', hm:funt([hm:bt(integer,-1),hm:bt(integer,-2)],hm:bt(integer,0),0)},
        {'bor', hm:funt([hm:bt(integer,-1),hm:bt(integer,-2)],hm:bt(integer,0),0)},
        {'bxor', hm:funt([hm:bt(integer,-1),hm:bt(integer,-2)],hm:bt(integer,0),0)},
        {'bsl', hm:funt([hm:bt(integer,-1),hm:bt(integer,-2)],hm:bt(integer,0),0)},
        {'bsr', hm:funt([hm:bt(integer,-1),hm:bt(integer,-2)],hm:bt(integer,0),0)},
        {'not', hm:funt([hm:bt(boolean,-1)],hm:bt(boolean,0),0)},
        {'and', hm:funt([hm:bt(boolean,-1),hm:bt(boolean,-2)],hm:bt(boolean,0),0)},
        {'or', hm:funt([hm:bt(boolean,-1),hm:bt(boolean,-2)],hm:bt(boolean,0),0)},
        {'xor', hm:funt([hm:bt(boolean,-1),hm:bt(boolean,-2)],hm:bt(boolean,0),0)},
        {'orelse', hm:funt([hm:bt(boolean,-1),hm:bt(boolean,-2)],hm:bt(boolean,0),0)},
        {'andalso', hm:funt([hm:bt(boolean,-1),hm:bt(boolean,-2)],hm:bt(boolean,0),0)},
        {'==', hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:bt(boolean,0),0)},
        {'/=', hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:bt(boolean,0),0)},
        {'=<', hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:bt(boolean,0),0)},
        {'<', hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:bt(boolean,0),0)},
        {'>=', hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:bt(boolean,0),0)},
        {'>', hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:bt(boolean,0),0)},
        {'=:=', hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:bt(boolean,0),0)},
        {'=/=', hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:bt(boolean,0),0)},
        {'++', hm:forall(a,[],
                hm:funt([hm:tcon("List",[hm:tvar(a,0)],-1),
                        hm:tcon("List",[hm:tvar(a,0)],-2)],
                        hm:tcon("List",[hm:tvar(a,0)],0),0),0)},
        {'--', hm:forall(a,[],
                hm:funt([hm:tcon("List",[hm:tvar(a,0)],-1),
                        hm:tcon("List",[hm:tvar(a,0)],-2)],
                        hm:tcon("List",[hm:tvar(a,0)],0),0),0)},
        {{is_atom,1}, hm:funt([hm:bt(atom,-1)],hm:bt(boolean,0),0)},
        {{is_integer,1}, hm:funt([hm:bt(integer,-1)],hm:bt(boolean,0),0)},
        {{is_list,1}, hm:forall(a,[],
                hm:funt([hm:tcon("List",[hm:tvar(a,0)],-1)],
                        hm:bt(boolean,0),0),0)},
        {{is_boolean,1}, hm:funt([hm:bt(boolean,-1)],hm:bt(boolean,0),0)},
        {'!', hm:forall(a,[{class,"Pid", hm:tvar(a,0)}],
                hm:funt([hm:tvar(a,-1),hm:tvar(b,-2)],hm:tvar(b,0),0),0) },
        {{self,0}, hm:funt([],hm:bt(pid,0),0)},
        {{spawn,1}, hm:funt([hm:funt([],hm:tvar(a,-10),-1)],hm:bt(pid,0),0)},
        {{spawn,2}, hm:funt([hm:bt(atom,-1),hm:funt([],hm:tvar(a,-20),-2)],hm:bt(pid,0),0)}
    ]).
