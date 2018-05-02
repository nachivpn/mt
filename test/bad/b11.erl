-module(b11).

 % Cons a elem with an elem!
badCons(Xs) ->
    [Head|Tail] = Xs, 
    [Head | Head].