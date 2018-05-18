%% @module Escript entry point.
-module(erly).

-export([main/1]).

main(Args0) ->
    Args = ["+{parse_transform, tidy}"] ++ 
    case lists:member("+noti",Args0) of
        true -> [];
        false -> ["+{parse_transform, etc}"]
    end ++ 
    case lists:member("+pe",Args0) of
        true -> ["+{parse_transform, pe}"];
        false -> []
    end ++ Args0,
    erl_compile2:compile_cmdline(Args).