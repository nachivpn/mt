-module (b1).
-compile({parse_transform, etc}).

f1() -> "" + 1.

f2() -> 1 + "".
