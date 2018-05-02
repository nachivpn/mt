-module(b19).

-type either(A) :: {left,A} | {right, A}.
-type dir(A) :: {left,A} | {right, A} | {fwd,A} | {bwd,A}.

extract({left,A}) -> A;
extract({right,A}) -> A.

% un-unifiable return types
foo12() -> extract({left,1.0});
foo12() -> extract({left,true}).