-module(b11).
-compile({parse_transform, etc}).

% X defined in one branch should not be visible in another!
foo(X) -> X div 3;
foo(_) -> X.