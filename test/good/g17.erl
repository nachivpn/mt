-module(g17).

ping() -> 1.0.

pong() -> pong.

% unused case can have branches of different types
foo(X) ->
    case X of
        ping -> ping();
        pong -> pong()
    end,
    trash.