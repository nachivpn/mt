-module(g3).
-compile({parse_transform, etc}).

ceq(X,Y) -> X == Y.

cne(X,Y) -> X /= Y.

clte(X,Y) -> X =< Y.

clt(X,Y) -> X < Y.

cgte(X,Y) -> X >= Y.

cgt (X,Y) -> X > Y.

cee (X,Y) -> X =:= Y.

cene (X,Y) -> X =/= Y.

foo1() -> "hello" == "world".

foo2() -> "hello" =:= 1.

foo3() -> 1.0 =/= 1.

foo5() -> 
    X = 1 div 5,
    X >= 5.0.
