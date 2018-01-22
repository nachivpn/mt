-module(hm).
-export([mgu/2]).

% Sub = [{Var,Type}]
% MSub = {succ, Sub} | {fail, Reason}

% comp :: (MSub, MSub) -> MSub
comp (X,Y) -> lift2(fun(P,Q) -> Q ++ P end, X, Y).

%  mgu :: (Type, Type) -> MSub
mgu ({funt, A1, B1}, {funt, A2, B2}) -> 
    X = mgu (A1, A2),
    case X of
        {succ, XSub} ->  
            Y = mgu (sub(B1, XSub),sub(B2, XSub)),
            comp(X,Y);
        {fail, Reason} ->
            {fail, Reason}
    end;
mgu ({tvar, V},T) ->
    Occ = occurs(V,T),
    if
        V == T      -> {succ, []};
        Occ         -> {fail,"occurs check"};
        true        -> {succ, [{V,T}]}
    end;
mgu (T,{tvar,V}) ->
    mgu ({tvar, V},T);
mgu (T,U) ->
    if
        T == U      -> {succ, []};
        true        -> {fail, "cannot unify"}
    end.

% sub :: (Type, Sub) -> Type
sub ({tvar, X}, Sub)    ->
    proplists:get_value(X, Sub);
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


% lift2 :: (Sub -> Sub -> Sub, MSub, MSub) -> MSub
lift2 (_, _, {fail, Reason})     -> {fail, Reason};
lift2 (_,{fail, Reason}, _)      -> {fail, Reason};
lift2 (F,{succ, Xs}, {succ, Ys}) -> {succ, F (Xs, Ys)}.
