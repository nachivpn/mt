-module (util).
-export([to_string/1]).

to_string(X) -> lists:flatten(io_lib:format("~p",[X])).