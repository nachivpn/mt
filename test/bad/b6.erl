-module(b6).

% undefined function foo/2
foo() -> X = fun foo/2, X.