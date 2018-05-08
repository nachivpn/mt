-module(b24).


f4(A,B,C) ->  
    if
	    A    -> X = "";
	    B    -> X = "";
        C    -> A = 2
    end,
    X.