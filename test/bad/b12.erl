-module(b11).

% X defined in one branch should not be visible in another!
foo(X) -> X div 3;
foo(_) -> X.