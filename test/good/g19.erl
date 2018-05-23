-module(g19).

ping() -> 1.0.

pong() -> 2.

% unused case can have branches of different types
foo(X) ->
    A = case X of
        ping -> ping();
        pong -> pong()
    end,
    A + 5.