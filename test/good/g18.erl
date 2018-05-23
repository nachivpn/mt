-module(g18).

ping() -> 1.0.

pong() -> 2.

% unused case can have branches of different types
foo(X) ->
    case X of
        ping -> ping();
        pong -> pong()
    end.