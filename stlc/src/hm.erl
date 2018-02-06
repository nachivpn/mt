-module(hm).
-export([infer/1]).

-type lterm() :: tuple().
-type type() :: tuple().
-type tvar() :: any().
-type env() :: [{tvar(),type()}].
-type sub() :: [{tvar(),type()}].

-type constraint() :: {type(), type()}.

%%%%%%%%%%%%% Inference function (main)

prettyCs([], S) -> S;
prettyCs([{T1,T2}|Cs],S) -> 
    S_ = stlc:prettify(S,T1),
    io:fwrite(" :==: "),
    S__ = stlc:prettify(S_,T2),
    io:fwrite("~n"),
    prettyCs(Cs,S__).

-spec infer(lterm()) -> type().
infer (Term) ->
    try inferE([],[],Term) of
        {T,Cs} -> 
            S = stlc:prettify([],T),
            io:fwrite("~nGenerated constraints are:~n"),
            S_ = prettyCs(Cs,S),
            Sub = solve(Cs,[]),
            io:fwrite("Inferred type: "),
            stlc:prettify(S_, subT(T,Sub)),
            io:fwrite("~n"),
            ok
    catch
        throw:Reason -> erlang:error("Type Error: " ++ Reason)
    end.

%%%%%%%%%%%% Inference algorithm

-spec inferE(env(), [constraint()], lterm()) -> {type(), [constraint()]}.
inferE (Env, Cs, {ident, X}) ->
    T = env:lookup(X,Env),
    case T of
        undefined -> throw("Unbound variable " ++ util:to_string(X));
        _ -> {freshen(T),Cs}
    end;
inferE (_, Cs, {int, _}) -> 
    {stlc:bt(int), Cs};
inferE (Env, Cs, {lam, {ident, X}, B}) ->
    A = env:fresh(),
    Env_ = env:extend (X,A,Env),
    {T,Cs_} = inferE (Env_, Cs, B),
    {stlc:funt(A,T), Cs_ };
inferE (Env, Cs, {app, F, A}) ->
    {T1,Cs1} = inferE(Env, Cs, F),
    {T2,Cs2} = inferE(Env, Cs1, A),
    V = env:fresh(),
    {V, Cs2 ++ [{T1, stlc:funt(T2,V)}]};
inferE (Env, Cs, {lets, {ident, X}, E1, E2}) ->
    {T1, Cs1} = inferE(Env, Cs, E1),
    Env_ = env:extend (X, generalize(T1,Env), Env),
    {T2, Cs2} = inferE(Env_, Cs1, E2),
    {T2, Cs2}.

%%%%%%%%%%%% Constraint solver

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

-spec unify(type(), type()) -> sub().
unify ({funt, A1, B1}, {funt, A2, B2}) -> 
    X = unify (A1, A2),
    Y = unify (subT(B1, X),subT(B2, X)),
    comp(Y,X);
unify ({tvar, V},T) ->
    Occ = occurs(V,T),
    if
        {tvar, V} == T  -> [];
        Occ             -> throw("failed occurs check");
        true            -> [{V,T}]
    end;
unify (T,{tvar,V}) ->
    unify ({tvar, V},T);
unify (T,U) ->
    if
        T == U      -> [];
        true        -> throw("Cannot unify " ++ util:to_string(T) ++ " & " ++ util:to_string(U))
    end.

%%%%%%%%%%%% Utilities

% Compose two substitutions
-spec comp(sub(), sub()) -> sub().
comp (X,Y) -> Y ++ X.

% Repetitive substution on a type
-spec subT(type(), sub()) -> type().
subT (T, []) -> T;
subT (T, [{V,VST}|Ss]) -> subT(subAll(T,V,VST), Ss).

% Repetitive substution on a constraint
-spec subC(constraint(), sub()) -> constraint().
subC ({T1,T2},S) -> {subT(T1,S),subT(T2,S)}.

% Substitute all occurences of a variable in a type with it's subtitute type
-spec subAll(type(), tvar(), type()) -> type().
subAll ({tvar, X}, V, T)  ->
    case X == V of
        true    ->  T;
        false   ->  {tvar, X}
    end;
subAll ({bt, T}, _, _)  ->
    {bt, T};
subAll ({funt, A, B},V,T)   ->
    {funt, subAll (A,V,T), subAll(B,V,T)};
subAll ({forall, {tvar, X}, A}, V, T)   ->
    case X == V of
        true    ->  A;  % avoids name capture!
        false   ->  {forall, {tvar, X}, subAll(A,V,T)}
    end.

-spec occurs(tvar(), type()) -> type().
occurs (V,{funt, A, B}) ->
    occurs(V,A) or occurs(V,B);
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
free ({funt, A, B})     -> sets:union(free (A),free (B));
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
            subAll(TAcc, V, env:fresh())
        end, stripbound(T), bound(T)).
