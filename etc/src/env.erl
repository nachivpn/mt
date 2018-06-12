-module(env).
-export([empty/0,lookup/2,extend/3,extendConstr/3,free/2
        ,is_bound/2,fmapV/2,lookupConstrs/2,default/0
        ,freeInEnv/1,length/1
        ,dumpModuleBindings/2,readModuleBindings/1
        ,lookupRemote/3,extendRecord/4,lookupRecord/2]).
-export_type([env/0]).

% Type checker ENvironment
-record(ten, 
    {   bindings        = [],
        constructors    = [],
        recFieldMap     = []
    }).

-type env() :: ten.

empty() -> #ten{}.

default() -> rt:defaultEnv().

% lookup :: (Var, [Var,Type])  -> Type
lookup(X,Env) -> proplists:get_value(X, Env#ten.bindings).

is_bound(X,Env) -> proplists:is_defined(X,Env#ten.bindings).

extend(X,A,Env) -> Env#ten{bindings = [{X,A} | Env#ten.bindings]}.

extendConstr(X,A,Env) -> Env#ten{constructors = [{X,A} | Env#ten.constructors]}.

free(X,Env) -> Env#ten{bindings = proplists:delete(X,Env#ten.bindings)}.

fmapV(F,Env) -> Env#ten{bindings = lists:map(fun ({Var,Type}) -> {Var,F(Type)} end, Env#ten.bindings)}.

lookupConstrs(X,Env) -> proplists:get_all_values(X,Env#ten.constructors).

%%%%%%%%% Records

extendRecord(R,A,RecFieldMap,Env) -> 
    extendRecFieldMap(R,RecFieldMap,extendConstr(R,A,Env)).

extendRecFieldMap(R,FieldMap,Env) -> 
    Env#ten{recFieldMap = [{R,FieldMap} | Env#ten.recFieldMap]}.

lookupRecord(X,Env) -> 
    case lookupConstrs(X,Env) of
        [A] -> {A,lookupRecFieldMap(X,Env)};
        []  -> undefined
    end.

lookupRecFieldMap(X,Env) -> 
    proplists:get_value(X, Env#ten.recFieldMap).

-spec freeInEnv(hm:env()) -> set:set(hm:tvar()).
freeInEnv (Env) ->
    lists:foldr(
            fun sets:union/2,
            sets:new(),
            lists:map(fun({_,T}) -> hm:free(T)end, Env#ten.bindings)).

length(Env) -> erlang:length(Env#ten.bindings).

dumpModuleBindings(Env,Module) ->
    InterfaceFile = lists:concat([Module,".ei"]),
    ModuleBindings = Env#ten.bindings -- (env:default())#ten.bindings,
    file:write_file(InterfaceFile,erlang:term_to_binary(ModuleBindings)).

readModuleBindings(Module) ->
    InterfaceFile = lists:concat([Module,".ei"]),
    {ok, Data} = file:read_file(InterfaceFile),
    erlang:binary_to_term(Data).

lookupRemote(Module,X,_) ->
    InterfaceFile = lists:concat([Module,".ei"]),
    case filelib:is_regular(InterfaceFile)of
        true -> lookup(X,#ten{bindings = readModuleBindings(Module)});
        false -> na
    end.
