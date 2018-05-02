-module(g8).

% function with different arities

foo() -> 0.

foo(X) -> foo(), X.

foo(X,Y) -> foo(), foo(X).

foo(X,Y,Z) -> foo(), foo(X), foo(X,Y).

bar() -> bar(1).

bar(X) -> bar().
