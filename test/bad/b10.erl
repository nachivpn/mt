-module(b10).
-compile({parse_transform, etc}).

% returns a list of integers
intTail([X|Xs]) -> X div 1, Xs.

% tries to add a string to a list of integers!
badHead(Xs) ->
    Ys = intTail(Xs), 
    [""| Ys].