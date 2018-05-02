-module(g7).

% simple mutually recursive functions

foo() -> ind(), bar().
bar() -> foo().
ind() -> 3.


even(N) -> (N == 0) or odd(N - 1).

odd(N) -> (N > 0) and even(N - 1).

