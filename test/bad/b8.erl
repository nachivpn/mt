-module(b8).
-compile({parse_transform, etc}).

% undefined function foo2
foo() -> foo2().