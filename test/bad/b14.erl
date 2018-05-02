-module(b14).

%  Overloaded constructors - simple
-type myList(A) :: {nil} | {cons, A, myList(A)}.
-type maybe(A) :: {nil} | {just, A}.


ex2({nil}) -> false;
ex2({just,A}) -> true;
ex2({cons,A,B}) -> true.
