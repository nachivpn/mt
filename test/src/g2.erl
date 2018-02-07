-module(g2).
-compile(export_all).

description() -> "Boolean expressions".

benot(X) -> not X.

beand (X,Y) -> X and Y.

beor (X,Y) -> X or Y.

bexor (X,Y) -> X xor Y.

beorelse (X,Y) -> X orelse Y.

beandalso (x,Y) -> X andalso Y.



