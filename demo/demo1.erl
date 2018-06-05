-module(demo1).
-compile(nowarn_unused_vars).
-compile(nowarn_unused_function).

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