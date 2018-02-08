-module(etc).
-import(erl_syntax,[
    function_clauses/1,
    clause_patterns/1,
    clause_body/1,
    clause_guard/1,
    type/1
]).

-export([parse_transform/2]).

-type lno() :: integer().
-type var() :: {var, lno(), atom()}.
-type arg() :: var().
-type gaurd() :: [tuple()].

-type expr() :: var() | {op,lno(),atom(),expr(),expr()}.
-type clause() :: {clause,lno(),[arg()],[gaurd()],[var()]}.

% var {var,4,'X'}
parse_transform(Forms,O) ->
    Functions = lists:filter(
        fun (Node) -> element(1, Node) == function end, Forms),
    lists:map(fun infer/1,Functions),
    Forms.

-spec infer(erl_syntax:syntaxTree()) -> hm:type().
infer (FunctionNode) ->
    try infer(env:empty(),FunctionNode) of
        {T,Cs} ->
            S = hm:prettify([],T),
            io:fwrite("~nGenerated constraints are:~n"),
            S_ = hm:prettyCs(Cs,S),
            Sub = hm:solve(Cs,hm:emptySub()),
            io:fwrite("Inferred type: "),
            stlc:prettify(S_, hm:subT(T,Sub)),
            io:fwrite("~n"),
            ok;
        Unknown   -> io:fwrite("~n WARNING: infer/2 result is not {Type,Constraints}, instead: ~p ~n",[Unknown])
    catch
        throw:Reason -> erlang:error("Type Error: " ++ Reason)
    end.

-spec infer(hm:env(), erl_syntax:syntaxTree()) -> {hm:type(),[hm:constraint()]}.
infer (Env,Node) -> 
    case type(Node) of
        function ->
            Clauses = function_clauses(Node),
            ClausesInfRes = lists:map(fun(C) -> infer(Env,C) end, Clauses),
            lists:nth(1,ClausesInfRes);   %supports only one clause!
        clause ->
            ClausePatterns = clause_patterns(Node),
            % Type assumption for every argument
            EnvEntries = lists:map(
                fun(Pattern) ->
                    case Pattern of
                        {var, _, X} -> {X,env:fresh()}
                    end
                end, ClausePatterns),
            Env_ = lists:foldr(
                fun({X,T}, AccEnv) -> env:extend(X,T,AccEnv) end, Env, EnvEntries),
            % ClauseGaurds = clause_guard(Node),
            Body = clause_body(Node),
            BodyInferResult = lists:map(fun (CB) -> infer(Env_, CB) end, Body),
            {T,Cs} = lists:nth(1,BodyInferResult),
            {lists:foldr (fun ({_,T},AccT) -> stlc:funt(T,AccT) end, T, EnvEntries) 
            , Cs };
        variable ->
            {var, _, X} = Node,
            case env:lookup(X,Env) of
                undefined   -> throw("Unbound variable " ++ util:to_string(X));
                T           -> {hm:freshen(T),[]}
            end;
        _ -> io:fwrite("INTERNAL: NOT implemented: ~p~n",[Node])
    end.