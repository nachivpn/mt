-module (b3).
-compile({parse_transform, etc}).

f1(X,Y) -> X + Y + 4.5.

f2(X,Y) -> Y = f1(X,Y), X div Y.
