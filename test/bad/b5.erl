-module(b5).

% defined twice! the type checker should reject this, not compiler

foo5(X,Y) -> X.

foo5(X,Y) -> Y.