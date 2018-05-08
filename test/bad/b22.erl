-module(b22).


f4(A,B,C,X) ->  
    X = 3.0,
    receive
	    A    -> X = "";
	    B    -> X = "";
        C    -> X = ""
    end,
    X.