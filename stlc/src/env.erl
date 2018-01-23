-module(env).
-export([fresh/0,lookup/2,extend/3,free/2]).

% fresh :: Type
fresh() -> stlc:tvar(make_ref()).

% lookup :: (Var, [Var,Type])  -> Type
lookup(X,Env) -> proplists:get_value(X, Env).

extend(X,A,Env) -> [{X,A} | Env].

free(X,Env) -> proplists:delete(X,Env).

