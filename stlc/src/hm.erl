-module(hm).
-export([mgu/2,infer/1]).


% Sub = [{Var,Type}]

%%%%%%%%%%%%% Inference function (main)

% infer :: Term -> Type
infer (Term) ->
    try inferE([],Term) of
        {S,T} -> stlc:pretty(sub(T,S))
    catch
        throw:Reason -> erlang:error("Type Error: " ++ Reason)
    end.

%%%%%%%%%%%% Inference algorithm
    
% inferE :: Term -> {Sub, Type}
inferE (Env, {ident, X}) ->
    T = env:lookup(X,Env),
    case T of
        undefined -> throw("Unbound variable " ++ util:to_string(X));
        _ -> {[],freshen(T)}
    end;
inferE (_, {int, _}) ->
    {[], stlc:bt(int)};
inferE (Env, {lam, {ident, X}, B}) ->
    A = env:fresh(),
    Env_ = env:extend (X,A,Env),
    {S,T} = inferE (Env_, B),
    {S,stlc:funt(sub(A,S),T)};
inferE (Env, {app, F, A}) ->
    {S1,T1} = inferE(Env, F),
    {S2,T2} = inferE(Env, A),
    V = env:fresh(),
    S3 = mgu(sub(T1,S2),stlc:funt(T2,V)),
    {comp(S3,comp(S2,S1)), sub(V,S3)};
inferE (Env, {lets, {ident, X}, E1, E2}) ->
    {S1,T1} = inferE(Env, E1),
    GenT1 = generalize(T1,Env),
    Env_ = env:extend (X, GenT1, Env),
    {S2,T2} = inferE(Env_, E2),
    {comp(S2,S1), T2}.
    
%%%%%%%%%%%% Unification algorithm

%  mgu :: (Type, Type) -> Sub
mgu ({funt, A1, B1}, {funt, A2, B2}) -> 
    X = mgu (A1, A2),
    Y = mgu (sub(B1, X),sub(B2, X)),
    comp(Y, X);
mgu ({tvar, V},T) ->
    Occ = occurs(V,T),
    if
        {tvar, V} == T  -> [];
        Occ             -> throw("failed occurs check");
        true            -> [{V,T}]
    end;
mgu (T,{tvar,V}) ->
    mgu ({tvar, V},T);
mgu (T,U) ->
    if
        T == U      -> [];
        true        -> throw("Cannot unify " ++ util:to_string(T) ++ " & " ++ util:to_string(U))
    end.

%%%%%%%%%%%% Utilities

% Compose two substitutions
% comp :: (Sub, Sub) -> Sub
comp (X,Y) -> Y ++ X.

% Repetitive substution
% sub :: (Type, Sub) -> Type
sub (T, []) -> T;
sub (T, [{V,VST}|Ss]) -> sub(subAll(T,V,VST), Ss).

% Substitute all occurences of a variable in a type with it's subtitute type
% subAll :: (Type, Var, Type) -> Type

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

% occurs :: (Var, Type) -> Type
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
% free :: (Type) -> Set Var
free ({bt, _})          -> sets:new();
free ({funt, A, B})     -> sets:union(free (A),free (B));
free ({tvar, A})        -> sets:add_element(A,sets:new());
free ({forall, {tvar, X}, A}) 
                        -> sets:del_element(X, free(A)).

% freeInEnv :: ([{Var,Type}]) -> Set Var
freeInEnv (VTs) ->
    lists:foldr(
            fun sets:union/2,
            sets:new(),
            lists:map(fun({_,T}) -> free(T) end, VTs)).

% converts a mono type to a poly type
% generalize :: (Type,Env) -> Type
generalize (Type,Env) ->
    Mono = free (Type),
    BoundInEnv = freeInEnv(Env),
    % Generalizable variables of a type are
    % monotype variables that are not bound in environment
    Generalizable = sets:subtract(Mono, BoundInEnv),
    bindGVs(sets:to_list(Generalizable),Type).

% bind generalized variables
% bindGVs :: ([Var], Type) -> Type
bindGVs ([],T)      -> T;
bindGVs ([X|Xs],T)  -> {forall, {tvar, X}, bindGVs(Xs,T)}.

% bound :: (Type) -> [Var]
bound ({forall, {tvar, X}, A}) -> [X | bound(A)];
bound (_) -> [].

% stripbound :: (Type) -> Type
stripbound ({forall, {tvar, _}, A}) -> stripbound(A);
stripbound (T) -> T.

% replace all bound variables with fresh variables
% freshen :: (Type) -> Type
freshen (T) ->
    lists:foldr(
        fun(V, TAcc)->
            subAll(TAcc, V, env:fresh())
        end, stripbound(T), bound(T)).
