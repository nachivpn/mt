-module(b15).
-compile({parse_transform, etc}).

% bad when

foo4(F,X,Y) when F -> F(X).