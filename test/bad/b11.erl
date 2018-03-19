-module(b11).
-compile({parse_transform, etc}).

 % Cons a elem with an elem!
badCons(Xs) ->
    [Head|Tail] = Xs, 
    [Head | Head].