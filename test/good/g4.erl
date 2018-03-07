-module (g4).
-compile({parse_transform, etc}).
-compile(export_all).


foo1() -> 1 + 1.5.

foo2() -> 1 + 2.

foo3() -> 1.5.

foo4() -> 
    X = foo3(),
    X;
foo4() -> 
    3.

add (A,B) -> A + B.

foo5(X,Y) -> 
    Z = add(X,Y),
    Z div Z.


foo6(X) -> X + 5.5.
