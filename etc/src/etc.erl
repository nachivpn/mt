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
            hm:prettify(S_, hm:subT(T,Sub)),
            io:fwrite("~n"),
            ok;
        Unknown   -> io:fwrite("~n WARNING: infer/2 result is not {Type,Constraints}, instead: ~p ~n",[Unknown])
    catch
        throw:Reason -> erlang:error("Type Error: " ++ Reason)
    end.

-spec infer(hm:env(), erl_syntax:syntaxTree()) -> {hm:type(),[hm:constraint()]}.
infer (Env,Node) -> 
    case type(Node) of
        integer -> 
            {integer,_,_} = Node,
            {hm:bt(integer),[]};
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
            {Env__, CsBody} =lists:foldl(
                fun(Expr, {Ei,Csi}) -> 
                    {Ei_,Csi_} = extendEnvExpr(Ei,Expr),
                    {Ei_, Csi ++ Csi_}
                end, {Env_,[]}, lists:droplast(Body)),
            {ReturnType, CsLast} = infer(Env__, lists:last(Body)),
            {lists:foldr (fun ({_,Typ},AccTyp) -> hm:funt(Typ,AccTyp) end, ReturnType, EnvEntries) 
            , CsBody ++ CsLast };
        variable ->
            {var, _, X} = Node,
            case env:lookup(X,Env) of
                undefined   -> throw("Unbound variable " ++ util:to_string(X));
                T           -> {hm:freshen(T),[]}
            end;
        application ->
            {call,_,F,[X]} = Node,
            {T1,Cs1} = infer(Env, F),
            {T2,Cs2} = infer(Env, X),
            V = env:fresh(),
            {V, Cs1 ++ Cs2 ++ [{T1, hm:funt(T2,V)}]};
        _ -> io:fwrite("INTERNAL: NOT implemented: ~p~n",[Node])
    end.

-spec extendEnvExpr(hm:env(), erl_syntax:syntaxTree()) -> {hm:env(),[hm:constraint()]}.
extendEnvExpr(Env,{match,LN,LNode,RNode}) ->
    LNodeType = type(LNode),
    if
        LNodeType == variable   -> 
            {var, _, X} = LNode,
            {RType, RCons} = infer(Env,RNode),
            Env_ = env:extend(X,RType,Env),
            {Env_, RCons};
        true   -> 
            {LType, LCons} = infer(Env,LNode),
            {RType, RCons} = infer(Env,RNode),
            {Env, LCons ++ RCons ++[{LType,RType}]}
    end.