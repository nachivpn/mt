-module(demo2).
-compile(nowarn_unused_vars).
-compile(nowarn_unused_function).

-etc(pe).
foo(F,G,X,P) ->
    T = {F(X),G(X)}, 
    case P(T) of
        true -> element(1,T);
        false -> element(2,T)
    end.