-module(stlc).
-export([ident/1,int/1,lam/2,app/2]).
-export([bt/1,funt/2, tvar/1]).

%% Term Constructors

ident (Name)    -> {ident, Name}.
int (N)         -> {int, N}.
lam (X, Exp)    -> {lam, X, Exp}.
app (E1, E2)    -> {app, E1, E2}.
% let (X, E1, E2) -> {lets, X, E1, E2}

%% Type constructors

bt (A)      -> {bt, A}.
funt (A,B)  -> {funt, A, B}.
tvar (A)    -> {tvar, A}.

% Example
idtype (A)  -> funt(A, A).
idterm (X)  -> lam (X, ident (X)).

