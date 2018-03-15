-module(b6).
-compile({parse_transform, etc}).

% a value cannot be applied!
foo() -> X = "", X().