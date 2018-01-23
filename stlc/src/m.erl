-module(m).
-export([lift2/3,bind/2,return/1,fail/1]).


return (X) -> {succ, X}.

fail (X) -> {fail, X}.

% lift2 :: ((Sub, Sub) -> Sub, MSub, MSub) -> MSub
lift2 (_, _, {fail, Reason})     -> {fail, Reason};
lift2 (_,{fail, Reason}, _)      -> {fail, Reason};
lift2 (F,{succ, Xs}, {succ, Ys}) -> {succ, F (Xs, Ys)}.

% bind :: (MSub, Sub -> MSub) -> MSub
bind ({fail, Reason}, _)    -> {fail, Reason};
bind ({succ, S}, F)        ->  F(S).