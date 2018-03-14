-module(g5).
-compile({parse_transform, etc}).

%Simple recursive functions

foo() -> X = foo(), X;
foo() -> "world".

foo1() -> foo1().

foo2() -> foo1().

fib(0) -> 0;
fib(1) -> 1;
fib(N) -> fib(N-1) + fib(N-2).

fac(0) -> 1;
fac(N) -> N * fac(N-1).


