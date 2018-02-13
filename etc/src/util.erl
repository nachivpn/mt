-module (util).
-export([to_string/1,intersperse/2,interFoldEffect/4,pairwiseChunk/1]).

to_string(X) -> lists:flatten(io_lib:format("~p",[X])).

intersperse(_,[]) -> [];
intersperse(_,[X]) -> [X];
intersperse(A,[X|Xs]) -> [X|[A|intersperse(A,Xs)]].

% a fold with an "effect intersperse"
interFoldEffect(_,_,B,[])         -> B;
interFoldEffect(F,_,B,[X])        -> F(X,B);
interFoldEffect(F,I,B,[X|Xs])     ->
    B_ = F(X,B), 
    I(), 
    interFoldEffect(F,I,B_,Xs).

pairwiseChunk ([])              -> {[],{nothing}};
pairwiseChunk ([X])             -> {[],{just,X}};
pairwiseChunk ([X|[Y|Tail]])    -> 
    {TailChunks, Rem} = pairwiseChunk(Tail),
    {[{X,Y} | TailChunks], Rem}.
