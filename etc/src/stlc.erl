-module(stlc).
-compile(export_all).

-type lterm() :: tuple().

%% Term Constructors

ident (Name)    -> {ident, Name}.
int (N)         -> {int, N}.
lam (X, Exp)    -> {lam, ident (X), Exp}.
app (E1, E2)    -> {app, E1, E2}.
lets (X, E1, E2) -> {lets, ident (X), E1, E2}.

% Example
% idtype (A)  -> funt(A, A).

idterm (X) -> lam (X, ident (X)).
idapp(X) -> app(idterm(X),idterm(X)).
sample() ->
    F = ident(f),
    lets(f,idterm(x),app(F,app(F,int(5)))).


-spec infer(lterm()) -> hm:type().
infer (Term) ->
    try inferE([],Term) of
        {T,Cs} -> 
            S = hm:prettify([],T),
            io:fwrite("~nGenerated constraints are:~n"),
            S_ = hm:prettyCs(Cs,S),
            Sub = hm:solve(Cs,hm:emptySub()),
            io:fwrite("Inferred type: "),
            hm:prettify(S_, hm:subT(T,Sub)),
            io:fwrite("~n"),
            ok
    catch
        throw:Reason -> erlang:error("Type Error: " ++ Reason)
    end.

%%%%%%%%%%%% Inference algorithm

-spec inferE(hm:env(), lterm()) -> {hm:type(), [hm:constraint()]}.
inferE (Env, {ident, X}) ->
    T = env:lookup(X,Env),
    case T of
        undefined -> throw("Unbound variable " ++ util:to_string(X));
        _ -> {hm:freshen(T),[]}
    end;
inferE (_, {int, _}) -> 
    {hm:bt(int), []};
inferE (Env, {lam, {ident, X}, B}) ->
    A = env:fresh(),
    Env_ = env:extend (X,A,Env),
    {T,Cs_} = inferE (Env_, B),
    {hm:funt(A,T), Cs_ };
inferE (Env, {app, F, A}) ->
    {T1,Cs1} = inferE(Env, F),
    {T2,Cs2} = inferE(Env, A),
    V = env:fresh(),
    {V, Cs1 ++ Cs2 ++ [{T1, hm:funt(T2,V)}]};
inferE (Env, {lets, {ident, X}, E1, E2}) ->
    {T1, Cs1} = inferE(Env, E1),
    Env_ = env:extend (X, hm:generalize(T1,Env), Env),
    {T2, Cs2} = inferE(Env_, E2),
    {T2, Cs1 ++ Cs2}.