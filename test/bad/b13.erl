-module(b13).
-compile({parse_transform, etc}).

-type err(A) :: {left, A} | {right, A}.
-type dir(A) :: {left,A} | {right, A} | {fwd,A} | {bwd,A}.


% polymorphic extract
extract({left,A}) -> A.
% extract({right,A}) -> A.

foo() -> extract(true).