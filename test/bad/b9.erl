-module(b9).
-compile({parse_transform, etc}).

foo(X,Y) -> X div 2.

bar(X) -> F = fun foo/2,F(X).