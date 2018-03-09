-module(da).
-export([parse_transform/2]).

getName (Fun) -> element(3,Fun).
getArgLen (Fun) -> element(4,Fun).
getClauses (Fun) -> element(5,Fun).

parse_transform(Forms,_) ->
    Functions = lists:filter(
        fun (Node) -> element(1, Node) == function end, Forms),
    Graph = digraph:new(),
    lists:map(fun(Fun) -> digraph:add_vertex(Graph,{getName(Fun),getArgLen(Fun)}) end, Functions),
    % For every function
    lists:map(fun(Fun) ->
        Clauses = getClauses(Fun),
        % a function needs the type of the function calls in it's body
        % hence edges are of from FromV -(needed_by)-> ToV
        ToV = {getName(Fun),getArgLen(Fun)},
        % For every clause
        lists:map(fun(C) ->
            % get calls in a clause 
            FromVs = getCallsFromClause(C),
            % add all the calls as edges to the graph
            lists:map(fun(FromV)-> 
                % io:fwrite("DEBUG: ~p => ~p ~n",[FromV,ToV]),
                digraph:add_edge(Graph,FromV,ToV) 
            end, FromVs)
        end, Clauses)
    end, Functions),
    SCCs = digraph_utils:strong_components(Graph),
    io:fwrite("DEBUG: SCCs = ~p~n",[SCCs]),
    SCCGraph = buildSccGraph(Graph,SCCs),
    SortedSCCs = digraph_utils:topsort(SCCGraph),
    io:fwrite("DEBUG: SortedSCCs = ~p~n",[SortedSCCs]),
    Forms.

getCallsFromClause(Clause) -> 
    getCallsFromBody(element(5,Clause)).

getCallsFromBody(Exprs) -> 
    lists:concat(
        lists:map(fun getCallsFromExpr/1,Exprs)).

getCallsFromExpr({call,_,{atom,_,Fn},FnArgs}) ->
    [ {Fn,length(FnArgs)} | 
        lists:concat(
            lists:map(fun getCallsFromExpr/1, FnArgs))];
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
