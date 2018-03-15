-module(da).
-export([mkSCCs/1]).

mkSCCs(Functions) ->
    Graph = digraph:new(),
    VFuns = lists:map(fun(Fun) -> 
        V = {util:getFnName(Fun),util:getFnArgLen(Fun)},
        digraph:add_vertex(Graph,V),
        {V,Fun}
    end, Functions),
    % For every function
    lists:map(fun(Fun) ->
        Clauses = util:getFnClauses(Fun),
        % a function needs the type of the function calls in it's body
        % hence edges are of from FromV -(needed_by)-> ToV
        ToV = {util:getFnName(Fun),util:getFnArgLen(Fun)},
        % For every clause
        lists:map(fun(C) ->
            % get calls in a clause 
            FromVs = getCallsFromClause(C),
            % add all the calls as edges to the graph
            lists:map(fun(FromV)-> 
                digraph:add_edge(Graph,FromV,ToV) 
            end, FromVs)
        end, Clauses)
    end, Functions),
    SCCs = digraph_utils:strong_components(Graph),
    SCCGraph = buildSccGraph(Graph,SCCs),
    SortedSCCs = digraph_utils:topsort(SCCGraph),
    lists:map(fun(SCC) ->
        lists:map(fun(V) ->
            element(2,lists:keyfind(V,1,VFuns))
        end, SCC)
    end, SortedSCCs).

getCallsFromClause(Clause) -> 
    getCallsFromBody(element(5,Clause)).

getCallsFromBody(Exprs) -> 
    lists:concat(
        lists:map(fun getCallsFromExpr/1,Exprs)).

% TODO: unmatched cases: 
% - call to fn in qualified with module, 
% - fun module:foo/x

% case of standard call: "FnAtom(Args)" 
getCallsFromExpr({call,_,{atom,_,Fn},FnArgs}) ->
    [ {Fn,length(FnArgs)} | 
        lists:concat(
            lists:map(fun getCallsFromExpr/1, FnArgs))];
% If the value "fun Fn/Arity" is present in the body,
% then the function (most probably) calls it!
getCallsFromExpr({'fun',_,{function,Fn,Arity}}) ->
    [ {Fn,Arity} ];
getCallsFromExpr(E) when is_tuple(E) ->
    Es_ = erlang:tuple_to_list(E),
    lists:concat(lists:map(fun getCallsFromExpr/1, Es_));
getCallsFromExpr(_) -> [].

-spec buildSccGraph(digraph:graph(),[[digraph:vertex()]]) -> digraph:graph().
buildSccGraph(FunDGraph,SCCs) -> 
    SCCGraph = digraph:new(),
    % add all SCC vertices to SCCGraph
    lists:map(fun(V) -> digraph:add_vertex(SCCGraph,V) end, SCCs),
    % add edges between SCCs using the (component) edges between members
    % If an edge exists between members of two different SCCs, 
    % then there exists an edge between the two SCCs in the exact same direction.
    % Since we separated strongly connected components as vertices in SCCGraph, 
    % there are no cycles in SCCGraph (PROOF?!)
    lists:map(fun(FromSCC) ->
        % for every element of an SCC
        lists:map(fun(FunV) ->
            % find (dependancies) neighbours that need the type of this FunV 
            % (FunV -needed_by-> Neighbour) 
            Neighbours = digraph:out_neighbours(FunDGraph,FunV),
            % find parents of neighbours
            ToSCCs = lists:map(fun(Nb) -> findParentSCC(SCCs,Nb) end, Neighbours),
            lists:map(fun(ToSCC) -> 
                digraph:add_edge(SCCGraph,FromSCC,ToSCC) end, ToSCCs)
        end, FromSCC)
    end, SCCs),
    SCCGraph.

findParentSCC(SCCs,FunV) -> 
    Parents = lists:dropwhile(
        fun(SCC) -> not lists:member(FunV,SCC) end, SCCs),
    lists:nth(1,Parents).
