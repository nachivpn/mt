-module(g2).
-compile({parse_transform, etc}).


benot(X) -> not X.

beand (X,Y) -> X and Y.

beor (X,Y) -> X or Y.

bexor (X,Y) -> X xor Y.

beorelse (X,Y) -> X orelse Y.

beandalso (X,Y) -> X andalso Y.



