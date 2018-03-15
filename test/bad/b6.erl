-module(b6).
-compile({parse_transform, etc}).

% undefined function foo/2
foo() -> X = fun foo/2, X.