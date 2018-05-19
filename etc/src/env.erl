-module(env).
-export([empty/0,lookup/2,extend/3,free/2
        ,is_bound/2,fmapV/2,lookupMulti/2,default/0
        ,freeInEnv/1,length/1
        ,dumpModuleBindings/2,readModuleBindings/1]).
-export_type([env/0]).

% Type checker ENvironment
-record(ten, 
    {   bindings = []
    }).

-type env() :: ten.

empty() -> #ten{}.

default() -> rt:defaultEnv().

% lookup :: (Var, [Var,Type])  -> Type
lookup(X,Env) -> proplists:get_value(X, Env#ten.bindings).

is_bound(X,Env) -> proplists:is_defined(X,Env#ten.bindings).

extend(X,A,Env) -> Env#ten{bindings = [{X,A} | Env#ten.bindings]}.

free(X,Env) -> Env#ten{bindings = proplists:delete(X,Env#ten.bindings)}.

fmapV(F,Env) -> Env#ten{bindings = lists:map(fun ({Var,Type}) -> {Var,F(Type)} end, Env#ten.bindings)}.

lookupMulti(X,Env) -> proplists:get_all_values(X,Env#ten.bindings).

-spec freeInEnv(hm:env()) -> set:set(hm:tvar()).
freeInEnv (Env) ->
    lists:foldr(
            fun sets:union/2,
            sets:new(),
            lists:map(fun({_,T}) -> hm:free(T)end, Env#ten.bindings)).

length(Env) -> erlang:length(Env#ten.bindings).

dumpModuleBindings(Env,Module) ->
    InterfaceFile = lists:concat([Module,".eti"]),
    ModuleBindings = Env#ten.bindings -- (env:default())#ten.bindings,
    file:write_file(InterfaceFile,erlang:term_to_binary(ModuleBindings)).

readModuleBindings(Module) ->
    InterfaceFile = lists:concat([Module,".eti"]),
    {ok, Data} = file:read_file(InterfaceFile),
    erlang:binary_to_term(Data).