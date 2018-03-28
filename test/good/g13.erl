-module(g13).
-compile({parse_transform, etc}).


-type either(A) :: {left, A} | {right, A}.
-type dir(A) :: {left,A} | {right,A} | {fwd,A} | {bwd,A}.


% polymorphic extract
extract({left,A}) -> A;
extract({right,A}) -> A.

% unfortunately, this type checks
foo() ->
    X = {fwd,1},
    extract(X).    
