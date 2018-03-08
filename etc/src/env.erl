-module(env).
-export([empty/0,lookup/2,extend/3,free/2,is_bound/2,mapV/2]).

empty() -> [].

% lookup :: (Var, [Var,Type])  -> Type
lookup(X,Env) -> proplists:get_value(X, Env).

is_bound(X,Env) -> proplists:is_defined(X,Env).

extend(X,A,Env) -> [{X,A} | Env].

free(X,Env) -> proplists:delete(X,Env).

mapV(F,Env) -> lists:map(fun ({Var,Type}) -> {Var,F(Type)} end, Env).