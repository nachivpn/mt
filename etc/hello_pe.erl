-module(hello_pe).
-compile(export_all).
-compile(nowarn_export_all).
-compile(nowarn_unused_vars).


-etc(skip).
tuplize([]) -> {};
tuplize([X|Xs]) -> {X,tuplize(Xs)}.

% tuplize([1.0,2.0,3.0]) = {1.0,{2.0,{3.0,{}}}}
-etc(pe).
evalTuplize() -> tuplize([1.0,2.0,3.0]).

-etc(skip).
server(Request) ->
    case Request of
        {get_file_name,Dir,File} -> Dir ++ File;
        {get_sum,X,Y} -> (X + Y)
    end.

-etc(pe).
client() -> server({get_sum,1.0,2.0}).

-etc(pe).
foo(F,G,X,P) ->
    T = {F(X),G(X)},
    case P(T) of
        true -> element(1,T);
        false -> element(2,T)
    end.