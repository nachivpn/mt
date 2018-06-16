-module(hello).
-compile(export_all).
-compile(nowarn_export_all).
-compile(nowarn_unused_vars).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Lists
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

append([H|T], Tail) ->
    [H|append(T, Tail)];
append([], Tail) ->
    Tail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Numeric types
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sum ([]) -> 0;
sum ([X|Xs]) -> X + sum(Xs).

average(Xs) -> sum(Xs) / length(Xs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Algebaric Data Types
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-type tree(A) :: nil
    | {node, A, tree(A), tree(A)}.

findNode(_,nil) -> 
    false;
findNode(N,{node,N,Lt,Rt}) ->
    true;
findNode(N,{node,_,Lt,Rt}) ->
    findNode(N, Lt) or findNode(N,Rt).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Overloaded constructors
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-type mlist(A) :: nil | {cons, A, mlist(A)}.

empty () -> nil.

flattenTree(nil) -> 
[];
flattenTree({node,N,Lt,Rt}) -> 
flattenTree(Lt) ++ [N|flattenTree(Rt)].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Messaging
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-type request()  :: {ping, pid()} 
    | {get_sum,pid(),integer(),integer()}.

server() ->
    receive
        {ping, Ping_PID} ->
            Ping_PID ! {pong, self()};
        {get_sum, Pong_PID, X, Y}  ->
            Pong_PID ! {sum, X + Y}
    end,
    server().

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Records
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-record(person,{
    name = "nachi" :: [char()]
    , phone  :: integer()
    , id
}).

createPerson() -> #person{phone = 1235, id = 0}.

updatePresonId(P,Id) -> P#person{id = Id}.

getId(P) -> P#person.id.

getPhone(P) -> P#person.phone.