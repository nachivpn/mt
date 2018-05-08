-module(g15).

f4(Arg) ->  
    case Arg of
	    [X|"A"]    -> "A";
	    [X|"B"]    -> "B";
        [X|"C"]   ->  "C"
    end,
    X.