-module(b29).

f(X) ->
    Z   = if
        X           -> 1;
        true        -> ""
    end.