-module (g6).

% collection of arbitrary tests

foo(F,X,Y,Z) -> F(X).

foo1(F,X,Y) -> F(X,Y).

foo2(X,Y) -> X().

foo3(X,Y) ->
    Y = 3,
    X(Y).

foo4(X,Y) ->
    3 = Y,
    X(Y).

foo5(X) ->
    3 = X(3),
    X(4).

foo6(F,X,Y) -> F(X);
foo6(F,X,Y) -> F(Y).

foo7(F,X,A,B) ->
    X = 3,
    F(X);
foo7(F,X,A,B) ->
    X = F(3),
    X.

foo8() -> foo8().

foo9(N) -> foo9(N + 1) + foo9(N + 2).

foo10(N) -> N.

foo11(N) -> N = 3, foo10(N).

foo12(N) -> N = "", foo10(N).

foo14() -> 1 + 1.5.

foo15(A,B) -> A + B.

foo16() -> X = 1, Y = 2, Y = foo15(X,Y), Y.
