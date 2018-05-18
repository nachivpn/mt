-module(tidy).
-export([parse_transform/2]).

parse_transform(Forms,_) ->
    lists:filter(fun(F) ->
        case F of
            {attribute,_,etc,skip}  -> false;
            {attribute,_,etc,pe}    -> false;
            _                       -> true
        end
    end, Forms).