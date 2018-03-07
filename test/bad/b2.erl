-module (b2).
-compile({parse_transform, etc}).

f3(X,Y) -> X + Y ;
f3(X,Y) -> X = "", X+ Y.

f4(X,Y) -> X + Y ;
f4(X,Y) -> "".





