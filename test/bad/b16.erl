-module(b16).

% bad when

qsort([]) ->
    [];
qsort([H | Hs]) ->
    {L, E, G} = partition(H, [H | Hs], {[], [], []}),
    qsort(L) ++ E ++ qsort(G).
 
partition(_, [], {L, E, G}) ->
    {L, E, G};
partition(Pivot, [H | List], {L, E, G}) when Pivot > H ->
    partition(Pivot, List, {[H | L], E, G});
partition(Pivot, [H | List], {L, E, G}) when {Pivot} -> % WTH tuple
    partition(Pivot, List, {L, E, [H | G]});
partition(Pivot, [H | List], {L, E, G}) when Pivot == H ->
partition(Pivot, List, {L, [H | E], G}).