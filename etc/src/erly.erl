%% @module Escript entry point.
-module(erly).

-export([main/1]).

main(Args0) ->
    Args = ["+{parse_transform, etc}","+{parse_transform, pe}" | Args0],
    erl_compile2:compile_cmdline(Args).