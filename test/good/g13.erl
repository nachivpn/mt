-module(g13).
% generic Overloaded constructors

-type either(A,B) :: {left, A} | {right, B}.
-type dir(A) :: {left,A} | {right,A} | {fwd,A} | {bwd,A}.

% polymorphic extract
extract({left,A}) -> A;
extract({right,A}) -> A.

foo() ->
    X = {fwd,1},
    extract(X).  

foo1() ->
    true = extract({left,true}).

fmap (_,{left,A}) -> {left,A};
fmap (F,{right,A}) -> {right,F(A)}.

bind ({right,A},F) -> F(A);
bind({left,A},_) -> {left,A}.

safe_div(_,0) -> {left,""};
safe_div(I,J) -> {right,I div J}.

is_right({right, _}) ->
    true;
is_right(_) ->
    false.

is_left({left, _}) ->
    true;
is_left(_) ->
    false.

get_rights([]) -> [];
get_rights([{right,X}|Xs]) -> [X|get_rights(Xs)];
get_rights([{left,_}|Xs]) -> get_rights(Xs).

app_get_rights() -> get_rights([{left,""},{right,2.0},{right,3.0},{left,""}]).
