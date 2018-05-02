-module(g12).

%  Overloaded constructors - simple
-type myList(A) :: {nil} | {cons, A, myList(A)}.
-type maybe(A) :: {nil} | {just, A}.
-type tree(A) :: {nil} | {node, A, tree(A), tree(A)}.

empty () -> {nil}.


findNode(_,{nil}) -> false;
findNode(N,{node,N,Lt,Rt}) -> true;
findNode(N,{node,_,Lt,Rt}) -> findNode(N, Lt) and findNode(N,Rt).

flattenTree({nil}) -> [];
flattenTree({node,N,Lt,Rt}) -> flattenTree(Lt) ++ [N | flattenTree(Rt)].

nameTree () -> {node, "First",empty (),nameTree ()}.

ex0 () -> {node, 1, empty (),empty ()}.

ex1 ({nil}) -> false;
ex1({just,_}) -> true.

ex2({nil}) -> false;
ex2({just,1}) -> true.
% ex2({cons,A,B}) -> true.
