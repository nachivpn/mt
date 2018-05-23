-module(b30).

f(X) ->
    Z   = case X of
            "hello" -> "world";
            "ping" -> pong
    end,
    Z.