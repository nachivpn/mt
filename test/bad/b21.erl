-module(b21).

-type either(A) :: {left,A} | {right, A}.
-type dir(A) :: {left,A} | {right, A} | {fwd,A} | {bwd,A}.


% un-unifiable argument types
foo12({left,false}) -> true;
foo12({right,1.0}) -> false.

