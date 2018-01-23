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
        _ -> m:return({[],T})
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
    end).

%%%%%%%%%%%% Unification algorithm

%  mgu :: (Type, Type) -> M Sub
mgu ({funt, A1, B1}, {funt, A2, B2}) -> 
    X = mgu (A1, A2),
    Y = m:bind (X, fun(XSub) -> 
            mgu (sub(B1, XSub),sub(B2, XSub)) 
        end),
    m:lift2(fun comp/2, X, Y);
mgu ({tvar, V},T) ->
    Occ = occurs(V,T),
    if
        V == T      -> m:return([]);
        Occ         -> m:fail("failed occurs check");
        true        -> m:return([{V,T}])
    end;
mgu (T,{tvar,V}) ->
    mgu ({tvar, V},T);
mgu (T,U) ->
    if
        T == U      -> m:return([]);
        true        -> m:fail("cannot unify")
    end.

%%%%%%%%%%%% Utilities

% comp :: (Sub, Sub) -> Sub
comp (X,Y) -> Y ++ X.

% sub :: (Type, Sub) -> Type
sub ({tvar, X}, Sub)  ->
    MT = proplists:lookup(X, Sub),
    case MT of
        none -> {tvar, X};
        {X,T} -> T
    end;
sub({bt, A},_)          ->
    {bt, A};
sub({funt, A, B},Sub)   ->
    {funt, sub (A,Sub), sub(B,Sub)}.

% occurs :: (Var, Type) -> Type
occurs (V,{funt, A, B}) ->
    occurs(V,A) or occurs(V,B);
occurs (_,{bt,_}) ->
    false;
occurs (V,{tvar, X}) ->
    V == X.