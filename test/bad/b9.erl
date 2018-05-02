-module(b9).

foo(X,Y) -> X div 2.

bar(X) -> F = fun foo/2,F(X).