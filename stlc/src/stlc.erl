-module(stlc).
-export([ident/1,int/1,lam/2,app/2]).
-export([bt/1,funt/2, tvar/1]).
-export([idterm/1,idapp/1]).
-compile(export_all).

%% Term Constructors

ident (Name)    -> {ident, Name}.
int (N)         -> {int, N}.
lam (X, Exp)    -> {lam, ident (X), Exp}.
app (E1, E2)    -> {app, E1, E2}.
% let (X, E1, E2) -> {lets, X, E1, E2}

%% Type constructors

bt (A)      -> {bt, A}.
funt (A,B)  -> {funt, A, B}.
tvar (A)    -> {tvar, A}.

% pretty :: Type -> IO
pretty(T) -> 
    prettify([],T),
    ok.

prettify(Env, {bt, A}) -> io:fwrite("~p", [A]), Env;
prettify(Env, {funt, A, B}) ->
    io:fwrite("(", []),
    Env_ = prettify(Env,A),
    io:fwrite("->", []),
    Env__ = prettify(Env_,B),
    io:fwrite(")", []),
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

% Example
% idtype (A)  -> funt(A, A).

idterm (X) -> lam (X, ident (X)).
idapp(X) -> app(idterm(X),idterm(X)).
sample() ->
    F = ident(f),
    X = ident(x),
    Y = ident(y),
    lam (f, lam (x, app(F, X))).