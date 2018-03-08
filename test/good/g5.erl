-module(g5).
-compile({parse_transform, etc}).

%Simple recursive functions

foo() -> X = foo(), X;
foo() -> "world".

foo1() -> foo1().

foo2() -> foo1().

foo(X,Y) -> foo(X,X) + foo(Y,Y).