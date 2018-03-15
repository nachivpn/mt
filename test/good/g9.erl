-module(g9).
-compile({parse_transform, etc}).

% different ways to call a function


foo(X,Y) -> X + Y.

bar() -> X = fun foo/2, X(1,2) div 3.