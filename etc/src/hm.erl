-module(hm).
-export([solve/1,prettyCs/2,prettify/2,emptySub/0,subT/2,freshen/1,generalize/2]).
-export([bt/1,funt/2,tvar/1,forall/2,pretty/1,subE/2]).
-export_type([constraint/0,env/0,type/0]).


-type tvar() :: any().
-type env() :: [{tvar(),type()}].
-type sub() :: maps:map(). % Map <tvar(),type()>

-type constraint() :: {type(), type()}.

%%%%%%%%%%%%% Type variable constructors

-type type() :: 
    {bt,type()}
    | {funt, [type()], type()} 
    | {tvar, type()}
    | {forall, type(), type()}.

bt (A)      -> {bt, A}.
funt (A,B)  -> {funt, A, B}.
tvar (A)    -> {tvar, A}.
forall (X,A)    -> {forall, tvar(X), A}.

%%%%%%%%%%%% Constraint solver

-spec solve([constraint()]) -> sub().
solve(Cs) -> solve(Cs, emptySub()).

-spec solve([constraint()], sub()) -> sub().
solve ([],Sub) -> Sub;
solve ([{T1,T2}|Cs],Sub) ->
    Sub_ = unify(T1,T2),
    solve(
        % apply new substitution to remaining constraints
        lists:map(fun(Cx) -> subC(Cx, Sub_) end, Cs), 
        % compose substitutions
        comp(Sub_,Sub)).

%%%%%%%%%%%% Unification algorithm

-spec unifyMany([type()],[type()]) -> sub().
unifyMany([],[])            -> emptySub();
unifyMany([],_)             -> erlang:error({type_error, "Number of arguments do not match"});
unifyMany(_,[])             -> erlang:error({type_error, "Number of arguments do not match"});
unifyMany ([A|As],[B|Bs])   ->
    Sub = unify(A,B),
    As_ = lists:map(fun(T) -> subT(T,Sub) end, As),
    Bs_ = lists:map(fun(T) -> subT(T,Sub) end, Bs),
    comp(unifyMany(As_,Bs_),Sub).

-spec unify(type(), type()) -> sub().
unify ({funt, As1, B1}, {funt, As2, B2}) -> 
    X = unifyMany (As1, As2),
    Y = unify (subT(B1, X),subT(B2, X)),
    comp(Y,X);
unify ({tvar, V},T) ->
    Occ = occurs(V,T),
    if
        {tvar, V} == T  -> emptySub();
        Occ             -> erlang:error({type_error, "Failed occurs check"});
        true            -> maps:put(V,T,emptySub())
    end;
unify (T,{tvar,V}) ->
    unify ({tvar, V},T);
unify (T,U) ->
    if
        T == U      -> emptySub();
        true        -> erlang:error({type_error, "Cannot unify " ++ util:to_string(T) ++ " & " ++ util:to_string(U)})
    end.

%%%%%%%%%%%% Utilities

-spec emptySub() -> sub().
emptySub () -> maps:new().

% Compose two substitutions
-spec comp(sub(), sub()) -> sub().
comp (X,Y) ->
    Y_ = maps:map( % apply subtitution X on every entry in Y
            fun(_,Type) -> subT(Type,X) end, Y),
    maps:merge(X,Y_).   % union (Y_, entries in X whose keys are not in Y)

% Apply a subtitution to a type
-spec subT(type(), sub()) -> type().
subT ({tvar, X}, Sub)  ->
    case maps:is_key(X,Sub) of
        true    ->  maps:get(X,Sub);
        false   ->  {tvar, X}
    end;
subT ({bt, T}, _)  ->
    {bt, T};
subT ({funt, As, B},Sub)   ->
    {funt, lists:map(fun(A) -> subT (A,Sub) end, As), subT(B,Sub)};
subT ({forall, {tvar, X}, A}, Sub)   ->
    case maps:is_key(X,Sub) of
        true    ->  {forall, {tvar, X}, subT(A,maps:remove(X,Sub))};  % avoids name capture!
        false   ->  {forall, {tvar, X}, subT(A,Sub)}
    end.

% Repetitive substution on a constraint
-spec subC(constraint(), sub()) -> constraint().
subC ({T1,T2},S) -> {subT(T1,S),subT(T2,S)}.

% Repetitive substution on a environment
-spec subE(env(), sub()) -> env().
subE (Env,S) -> env:mapV(fun(T) -> subT(T,S) end, Env).

-spec occurs(tvar(), type()) -> boolean().
occurs (V,{funt, As, B}) ->
    lists:any(fun(A) -> occurs(V,A) end, As) or occurs(V,B);
occurs (_,{bt,_}) ->
    false;
occurs (V,{tvar, X}) ->
    V == X;
occurs (V,{forall, {tvar, X}, A}) ->
    case X == V of
        true -> false ;  
        false -> occurs (V,A)
    end.

% All free type variables in the given type
-spec free(type()) -> set:set(tvar()).
free ({bt, _})          -> sets:new();
free ({funt, As, B})     -> 
    sets:union(
        lists:foldr(
            fun(A, AccSet) -> sets:union(free(A),AccSet) end
            , sets:new(), As)
        , free (B));
free ({tvar, A})        -> sets:add_element(A,sets:new());
free ({forall, {tvar, X}, A}) 
                        -> sets:del_element(X, free(A)).

-spec freeInEnv(env()) -> set:set(tvar()).
freeInEnv (VTs) ->
    lists:foldr(
            fun sets:union/2,
            sets:new(),
            lists:map(fun({_,T}) -> free(T) end, VTs)).

% converts a mono type to a poly type
-spec generalize(type(),env()) -> type().
generalize (Type,Env) ->
    Mono = free (Type),
    BoundInEnv = freeInEnv(Env),
    % Generalizable variables of a type are
    % monotype variables that are not bound in environment
    Generalizable = sets:subtract(Mono, BoundInEnv),
    bindGVs(sets:to_list(Generalizable),Type).

% bind generalized variables
-spec bindGVs([tvar()],type()) -> type().
bindGVs ([],T)      -> T;
bindGVs ([X|Xs],T)  -> {forall, {tvar, X}, bindGVs(Xs,T)}.

-spec bound(type()) -> [tvar()].
bound ({forall, {tvar, X}, A}) -> [X | bound(A)];
bound (_) -> [].

-spec stripbound(type()) -> type().
stripbound ({forall, {tvar, _}, A}) -> stripbound(A);
stripbound (T) -> T.

% replace all bound variables with fresh variables
-spec freshen (type()) -> type().
freshen (T) ->
    lists:foldr(
        fun(V, TAcc)->
            subT(TAcc, maps:put(V,env:fresh(),emptySub()))
        end, stripbound(T), bound(T)).

% pretty :: Type -> IO
pretty(T) -> 
    prettify([],T),
    ok.

% Stateful pretty printer
prettify(Env, {bt, A}) -> io:fwrite("~p", [A]), Env;
prettify(Env, {funt, As, B}) ->
    io:fwrite("(", []),
    Env_ = util:interFoldEffect(
        fun(A,E) -> prettify(E,A) end
        , fun() -> io:fwrite(",") end
        , Env, As),
    io:fwrite(")", []),
    io:fwrite("->", []),
    Env__ = prettify(Env_,B),
    Env__;
prettify(Env, {tvar, A}) ->
    X = env:lookup(A, Env),
    case X of
        undefined -> 
            L = length(Env) + 65,
            io:fwrite("~c", [L]),
            env:extend(A,L,Env);       
        _         -> 
            io:fwrite("~c", [X]),
            Env
    end.

prettyCs([], S) -> S;
prettyCs([{T1,T2}|Cs],S) -> 
    S_ = prettify(S,T1),
    io:fwrite(" :==: "),
    S__ = prettify(S_,T2),
    io:fwrite("~n"),
    prettyCs(Cs,S__).
