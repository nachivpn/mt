-module(b23).


f4(A,B,C) ->  
    receive
	    A    -> X = "";
	    B    -> X = "";
        C    -> A = 2
    end,
    X.