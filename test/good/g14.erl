-module(g14).

f1(X) ->
    case X of
	    true -> A = 1, B = 7;
	    false -> B = 6
    end,
    B.

f2(X) ->
    if
	    X       -> A = 1, B = 7;
	    true    -> B = 6
    end,
    B. 

f3(A,B,C) ->
    receive
	    A    -> X = 1;
	    B    -> X = 6;
        C    -> X = 5
    end,
    X.

f4(A,B,C,X) ->
    receive
	    A    -> X = 1;
	    B    -> X = 6;
        C    -> X = 5
    end,
    X.

