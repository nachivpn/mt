-module(b5).
-compile({parse_transform, etc}).

% defined twice! the type checker should reject this, not compiler

foo5(X,Y) -> X.

foo5(X,Y) -> Y.