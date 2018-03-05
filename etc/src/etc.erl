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

-type expr() :: var() | {op,lno(),atom(),expr(),expr()}.

parse_transform(Forms,_) ->
    Functions = lists:filter(
        fun (Node) -> element(1, Node) == function end, Forms),
    try
        lists:foldl(
            fun(F, AccEnv) ->
                FunName     = element(4, erl_syntax:function_name(F)),
                FreshT      = env:fresh(),
                AccEnv_     = env:extend(FunName, FreshT, AccEnv),
                % AccEnv_ is used for inference (only) to allow type checking recursive fns
                {InfT, InfCs, InfPs}  = infer(AccEnv_, F),
                Sub         = hm:solve(InfCs ++ unify(InfT, FreshT)),
                T           = hm:subT(InfT, Sub),
                Ps          = hm:subPs(InfPs,Sub), 
                RemPs      = hm:solvePreds(rt:defaultClasses(), Ps),
                PolyT       = hm:generalize(T, AccEnv, RemPs),
                env:extend(FunName, PolyT, AccEnv)
            end
        , rt:defaultEnv(), Functions)
    of  
        Env -> 
            lists:map(fun({X,T}) -> 
                io:fwrite("~p :: ",[X]), 
                hm:pretty(T), 
                io:fwrite("~n",[])
            end, lists:reverse(Env))
    catch
        error:{type_error,Reason} -> erlang:error("Type Error: " ++ Reason)
    end,
    Forms.
    

-spec infer(hm:env(), erl_syntax:syntaxTree()) -> {hm:type(),[hm:constraint()],[hm:predicate()]}.
infer (Env,Node) -> 
    case type(Node) of
        integer -> 
            {integer,_,_} = Node,
            X = env:fresh(),
            {X,[],[{"Num",X}]};
        string ->
            {string,_,_} = Node,
            {hm:bt(string),[],[]};
        float ->
            {float,_,_} = Node,
            X = env:fresh(),
            {X,[],[{"Fractional",X}]};
        function ->
            Clauses = function_clauses(Node),
            % list of clause inference results
            ClausesInfRes = lists:map(fun(C) -> infer(Env,C) end, Clauses),
            % "flatten" clause inference results
            {InfTypes, InfCs, InfPs} = lists:foldr(
                fun({T,Cs,Ps}, {AccTypes,AccCs,AccPs}) 
                    -> {[T|AccTypes], Cs ++ AccCs, Ps ++ AccPs} 
                end
                , {[],[],[]}, ClausesInfRes),
            % Unify the types of all clauses 
            UniCs = unify(InfTypes),
            % pick the type of any one clause as the type of fn
            {lists:last(InfTypes), InfCs ++ UniCs, InfPs};
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
            {Env__, CsBody, PsBody} =lists:foldl(
                fun(Expr, {Ei,Csi,Psi}) -> 
                    {Ei_,Csi_,Psi_} = checkExpr(Ei,Expr),
                    {Ei_, Csi ++ Csi_, Psi ++ Psi_}
                end, {Env_,[],[]}, lists:droplast(Body)),
            {ReturnType, CsLast, PsLast} = infer(Env__, lists:last(Body)),
            {hm:funt(
                lists:map (fun ({_,Typ}) -> Typ end, EnvEntries)
                , ReturnType)
            , CsBody ++ CsLast 
            , PsBody ++ PsLast};
        variable ->
            {var, _, X} = Node,
            {T, Ps} = lookup(X, Env),
            {T, [], Ps};
        application ->
            {call,_,F,Args} = Node,
            {T1,Cs1,Ps1} = infer(Env, F),            
            {T2,Cs2,Ps2} = lists:foldl(
                fun(X, {AccT,AccCs,AccPs}) -> 
                    {T,Cs,Ps} = infer(Env,X),
                    {AccT ++ [T], AccCs ++ Cs, AccPs ++ Ps}
                end
                , {[],[],[]}, Args),
            V = env:fresh(),
            {V, Cs1 ++ Cs2 ++ unify(T1, hm:funt(T2,V)), Ps1 ++ Ps2};
        infix_expr ->
            {op,_,Op,E1,E2} = Node,
            {T, Ps} = lookup(Op, Env),
            {T1, Cs1, Ps1} = infer(Env, E1),
            {T2, Cs2, Ps2} = infer(Env, E2),
            V = env:fresh(),
            {V, Cs1 ++ Cs2 ++ unify(T, hm:funt([T1,T2],V)), Ps ++ Ps1 ++ Ps2};
        atom ->
            {atom,_,X} = Node,
            {T, Ps} = lookup(X,Env),
            {T,[],Ps};
        _ -> io:fwrite("INTERNAL: NOT implemented: ~p~n",[Node])
    end.

-spec checkExpr(hm:env(), erl_syntax:syntaxTree()) -> {hm:env(),[hm:constraint()],[hm:predicate()]}.
checkExpr(Env,{match,_,LNode,RNode}) ->
    {Env_, Cons1, Ps} = checkExpr(Env,LNode),
    {LType, Cons2, PsL} = infer(Env_,LNode),
    {RType, Cons3, PsR} = infer(Env,RNode),
    {Env_, Cons1 ++ Cons2 ++ Cons3 ++ [{LType,RType}], Ps ++ PsL ++ PsR};
checkExpr(Env,{var,_,X}) ->
    case env:is_bound(X,Env) of
        true    -> {Env,[],[]};
        false   -> {env:extend(X,env:fresh(),Env), [],[]}
    end;
checkExpr(Env,ExprNode) -> 
    {_,Constraints,Ps} = infer(Env, ExprNode),
    {Env,Constraints,Ps}.


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

-spec lookup(hm:tvar(),hm:env()) -> {hm:type(),[hm:predicate()]}.
lookup(X,Env) ->
    case env:lookup(X,Env) of
        undefined   -> erlang:error({type_error,util:to_string(X) ++ " not bound!"});
        T           -> hm:freshen(T)
    end.