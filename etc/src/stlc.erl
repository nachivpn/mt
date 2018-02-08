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
lets (X, E1, E2) -> {lets, ident (X), E1, E2}.

%% Type constructors

bt (A)      -> {bt, A}.
funt (A,B)  -> {funt, A, B}.
tvar (A)    -> {tvar, A}.
forall (X,A)    -> {forall, tvar(X), A}.

% Example
% idtype (A)  -> funt(A, A).

idterm (X) -> lam (X, ident (X)).
idapp(X) -> app(idterm(X),idterm(X)).
sample() ->
    F = ident(f),
    lets(f,idterm(x),app(F,app(F,int(5)))).