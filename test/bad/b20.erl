-module(b20).

-type either(A) :: {left,A} | {right, A}.
-type dir(A) :: {left,A} | {right, A} | {fwd,A} | {bwd,A}.

% % % polymorphic extract
extract({left,A}) -> A;
extract({right,A}) -> A.

foo12() -> extract({left,1});
foo12() -> extract({left,true}).