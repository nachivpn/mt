-module(hm).
-export([mgu/2,infer/1]).


% Sub = [{Var,Type}]

%%%%%%%%%%%%% Inference function (main)

% infer :: Term -> Type
infer (Term) ->
    IT = inferE([],Term),
    case IT of
        {fail,Reason} -> erlang:error("Error: " ++ Reason);
        {succ,{S,T}} -> stlc:pretty(sub(T,S))
    end.

%%%%%%%%%%%% Inference algorithm
    
% inferE :: Term -> M {Sub, Type}
inferE (Env, {ident, X}) ->
    T = env:lookup(X,Env),
    case T of
        undefined -> m:fail("Unbound variable " ++ 
            lists:flatten(io_lib:format("~p",[X])));
        _ -> m:return({[],freshen(T)})
    end;
inferE (_, {int, _}) ->
    m:return({[], stlc:bt(int)});
inferE (Env, {lam, {ident, X}, B}) ->
    A = env:fresh(),
    Env_ = env:extend (X,A,Env),
    MST = inferE (Env_, B),
    m:bind(MST, fun({S,T}) ->
            m:return({S,stlc:funt(sub(A,S),T)})
        end);
inferE (Env, {app, F, A}) ->
    X = inferE(Env, F),
    Y = inferE(Env, A),
    V = env:fresh(),
    m:bind(X, fun({S1,T1}) -> 
        m:bind(Y, fun ({S2,T2}) ->
            MS3 = mgu(sub(T1,S2),stlc:funt(T2,V)),
            m:bind(MS3, fun (S3) ->
                m:return({comp(S3,comp(S2,S1)), sub(V,S3)})
            end)
        end)
    end);
inferE (Env, {lets, {ident, X}, E1, E2}) ->
    ST1 = inferE(Env, E1),
    m:bind(ST1, fun({S1,T1}) ->
        GenT1 = generalize(T1,Env),
        Env_ = env:extend (X, GenT1, Env),
        ST2 = inferE(Env_, E2),
        m:bind(ST2, fun({S2,T2}) ->
            m:return({comp(S2,S1), T2})
        end)
    end).
    
%%%%%%%%%%%% Unification algorithm

%  mgu :: (Type, Type) -> M Sub
mgu ({funt, A1, B1}, {funt, A2, B2}) -> 
    X = mgu (A1, A2),
    Y = m:bind (X, fun(XSub) -> 
            mgu (sub(B1, XSub),sub(B2, XSub)) 
        end),
    m:lift2(fun comp/2, Y, X);
mgu ({tvar, V},T) ->
    Occ = occurs(V,T),
    if
        {tvar, V} == T  -> m:return([]);
        Occ             -> m:fail("failed occurs check");
        true            -> m:return([{V,T}])
    end;
mgu (T,{tvar,V}) ->
    mgu ({tvar, V},T);
mgu (T,U) ->
    if
        T == U      -> m:return([]);
        true        -> m:fail("cannot unify")
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

% free :: ([{Var,Type}]) -> Set Var
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
