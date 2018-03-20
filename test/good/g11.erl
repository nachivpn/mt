-module(g11).
-compile({parse_transform, etc}).


% User defined data types

-type tree(A) :: {nil} | {node, A, tree(A), tree(A)}.

emptyTree () -> {nil}.
% 
findNode(_,{nil}) -> false;
findNode(N,{node,N,Lt,Rt}) -> true;
findNode(N,{node,_,Lt,Rt}) -> findNode(N, Lt) and findNode(N,Rt).

flattenTree({nil}) -> [];
flattenTree({node,N,Lt,Rt}) -> flattenTree(Lt) ++ [N | flattenTree(Rt)].

nameTree () -> {node, "First",emptyTree (),nameTree ()}.