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
            % S = hm:prettify([],T),
            % io:fwrite("~nGenerated constraints are:~n"),
            % S_ = hm:prettyCs(Cs,S),
            Sub = hm:solve(Cs,hm:emptySub()),
            io:fwrite("Inferred type: "),
            hm:pretty(hm:subT(T,Sub)),
            io:fwrite("~n"),
            ok;
        Unknown   -> io:fwrite("~n WARNING: infer/2 result is not {Type,Constraints}, instead: ~p ~n",[Unknown])
    catch
        error:{type_error,Reason} -> erlang:error("Type Error: " ++ Reason)
    end.

-spec infer(hm:env(), erl_syntax:syntaxTree()) -> {hm:type(),[hm:constraint()]}.
infer (Env,Node) -> 
    case type(Node) of
        integer -> 
            {integer,_,_} = Node,
            {hm:bt(integer),[]};
        string ->
            {string,_,_} = Node,
            {hm:bt(string),[]};
        float ->
            {float,_,_} = Node,
            {hm:bt(float),[]};
        function ->
            Clauses = function_clauses(Node),
            % list of clause inference results
            ClausesInfRes = lists:map(fun(C) -> infer(Env,C) end, Clauses),
            % "flatten" clause inference results
            {InfTypes, InfCs} = lists:foldr(
                fun({T,Cs},{AccTypes,AccCs}) -> {[T|AccTypes], Cs ++ AccCs} end
                , {[],[]}, ClausesInfRes),
            % Unify the types of all clauses 
            UniCs = unify(InfTypes),
            % pick the type of any one clause as the type of fn
            {lists:last(InfTypes), InfCs ++ UniCs};
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
                    {Ei_,Csi_} = checkExpr(Ei,Expr),
                    {Ei_, Csi ++ Csi_}
                end, {Env_,[]}, lists:droplast(Body)),
            {ReturnType, CsLast} = infer(Env__, lists:last(Body)),
            {hm:funt(
                lists:map (fun ({_,Typ}) -> Typ end, EnvEntries)
                , ReturnType)
            , CsBody ++ CsLast };
        variable ->
            {var, _, X} = Node,
            case env:lookup(X,Env) of
                undefined   -> erlang:error({type_error,"Unbound variable " ++ util:to_string(X)});
                T           -> {hm:freshen(T),[]}
            end;
        application ->
            {call,_,F,Args} = Node,
            {T1,Cs1} = infer(Env, F),            
            {T2,Cs2} = lists:foldl(
                fun(X, {AccT,AccCs}) -> 
                    {T,Cs} = infer(Env,X),
                    {AccT ++ [T], AccCs ++ Cs}
                end
                , {[],[]}, Args),
            V = env:fresh(),
            {V, Cs1 ++ Cs2 ++ unify(T1, hm:funt(T2,V))};
        _ -> io:fwrite("INTERNAL: NOT implemented: ~p~n",[Node])
    end.

-spec checkExpr(hm:env(), erl_syntax:syntaxTree()) -> {hm:env(),[hm:constraint()]}.
checkExpr(Env,{match,_,LNode,RNode}) ->
    {Env_,Cons1} = checkExpr(Env,LNode),
    {LType, Cons2} = infer(Env_,LNode),
    {RType, Cons3} = infer(Env,RNode),
    {Env_, Cons1 ++ Cons2 ++ Cons3 ++ [{LType,RType}]};
checkExpr(Env,{var,_,X}) ->
    case env:is_bound(X,Env) of
        true    -> {Env,[]};
        false   -> {env:extend(X,env:fresh(),Env), []}
    end;
checkExpr(Env,ExprNode) -> 
    {_,Constraints} = infer(Env, ExprNode),
    {Env,Constraints}.


%%%%%%%%%%%%%%%%%% Utilities

% "pseudo unify" which returns constraints
-spec unify([hm:type()]) -> [hm:constraint()].
unify(Types) ->
    {Constraints, RemType} = util:pairwiseChunk(Types),
    RemConstraints = 
        case RemType of
            {nothing} -> [];
            {just, X} -> 
                case length(Constraints) of
                    L when L > 0    -> [{X, element(2,lists:last(Constraints))}];
                    _               -> []
                end
        end,
    Constraints ++ RemConstraints.

% "pseudo unify" which returns constraints
-spec unify(hm:type(),hm:type()) -> [hm:constraint()].
unify(Type1,Type2) -> [{Type1,Type2}].