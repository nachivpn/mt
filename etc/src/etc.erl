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
    SCCs = da:mkSCCs(Functions),
    try
        lists:foldl(fun(SCC, AccEnv) ->
               typeCheckSCC(SCC,AccEnv)
        end, rt:defaultEnv(), SCCs)
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

typeCheckSCC(Functions,Env) ->
    % assign a fresh type variable to every function
    FreshEnv = lists:foldl(fun(F,AccEnv) -> 
        FunQName = util:getFnQName(F), 
        env:extend(FunQName, hm:fresh(util:getLn(F)), AccEnv)
    end, Env, Functions),
    {InfCs,InfPs} = lists:foldl(fun(F,{AccCs,AccPs}) ->
        FunQName = util:getFnQName(F),
        {T,Cs,Ps} = infer(FreshEnv,F),
        {FreshT,_} = lookup(FunQName, FreshEnv, util:getLn(F)),
        { unify(T, FreshT) ++ Cs ++ AccCs
        , Ps ++ AccPs}
    end, {[],[]}, Functions),
    Sub     = hm:solve(InfCs),
    Ps      = hm:subPs(InfPs,Sub),
    RemPs   = hm:solvePreds(rt:defaultClasses(), Ps),
    SubdEnv = hm:subE(FreshEnv,Sub), 
    lists:foldl(fun(F, AccEnv) ->
        FunQName = util:getFnQName(F),
        %lookup type from the substituted environment
        {T,_}  = lookup(FunQName, SubdEnv, util:getLn(F)),
        % generalize type wrt given environment
        PolyT   = hm:generalize(T, AccEnv, RemPs),
        env:extend(FunQName, PolyT, AccEnv)
    end, Env, Functions).

    

-spec infer(hm:env(), erl_syntax:syntaxTree()) -> {hm:type(),[hm:constraint()],[hm:predicate()]}.
infer (Env,Node) -> 
    case type(Node) of
        integer -> 
            {integer,L,_} = Node,
            X = hm:fresh(L),
            {X,[],[{"Num",X}]};
        string ->
            {string,L,_} = Node,
            {hm:bt(string,L),[],[]};
        float ->
            {float,L,_} = Node,
            {hm:bt(float,L),[],[]};
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
            L = element(2,Node),
            % Infer types of arguments (which are in the form of patterns)
            % Env_ is Env extended with arg variables
            {ArgTypes, Env_, CsArgs, PsArgs} = inferPatterns(Env,ClausePatterns),
            % ClauseGaurds = clause_guard(Node),
            Body = clause_body(Node),
            {Env__, CsBody, PsBody} =lists:foldl(
                fun(Expr, {Ei,Csi,Psi}) -> 
                    {Ei_,Csi_,Psi_} = checkExpr(Ei,Expr),
                    {Ei_, Csi ++ Csi_, Psi ++ Psi_}
                end, {Env_,[],[]}, lists:droplast(Body)),
            {ReturnType, CsLast, PsLast} = infer(Env__, lists:last(Body)),
            {hm:funt(ArgTypes,ReturnType,L)
            , CsArgs ++ CsBody ++ CsLast 
            , PsArgs ++ PsBody ++ PsLast};
        variable ->
            {var, L, X} = Node,
            {T, Ps} = lookup(X, Env, L),
            {T, [], Ps};
        application ->
            {call,L,F,Args} = Node,
            {T1,Cs1,Ps1} = inferFn(Env,F,length(Args)),   
            {T2,Cs2,Ps2} = lists:foldl(
                fun(X, {AccT,AccCs,AccPs}) -> 
                    {T,Cs,Ps} = infer(Env,X),
                    {AccT ++ [T], AccCs ++ Cs, AccPs ++ Ps}
                end
                , {[],[],[]}, Args),
            V = hm:fresh(L),
            {V, Cs1 ++ Cs2 ++ unify(T1, hm:funt(T2,V,L)), Ps1 ++ Ps2};
        infix_expr ->
            {op,L,Op,E1,E2} = Node,
            {T, Ps} = lookup(Op, Env,L),
            {T1, Cs1, Ps1} = infer(Env, E1),
            {T2, Cs2, Ps2} = infer(Env, E2),
            V = hm:fresh(L),
            {V, Cs1 ++ Cs2 ++ unify(T, hm:funt([T1,T2],V,L)), Ps ++ Ps1 ++ Ps2};
        atom ->
            {atom,L,X} = Node,
            case X of
                B when (B == true) or (B == false) -> 
                        {hm:bt(boolean,L),[],[]};
                _ ->    {hm:bt(atom,L),[],[]}
            end;
        implicit_fun ->
            {'fun',L,{function,X,ArgLen}} = Node,
            {T, Ps} = lookup({X,ArgLen},Env,L), {T,[],Ps};
        nil ->
            {nil,L} = Node,
            {hm:tcon("List",L,[hm:fresh(L)]),[],[]};
        list -> 
            {cons,L,H,T} = Node,
            {HType,HCs,HPs} = infer(Env, H),
            {TType,TCs,TPs} = infer(Env, T),
            case TType of
                 {tcon, _, "List", [A]}  -> {TType, HCs ++ TCs ++ unify(HType,A) , HPs ++ TPs};
                 _                      -> erlang:error({type_error,
                    " Tail must be a list type on line "++ util:to_string(L)})
            end;
        X -> erlang:error({type_error," Cannot infer type of " 
            ++ util:to_string(Node) ++ " with node type "++ util:to_string(X)})
    end.

-spec checkExpr(hm:env(), erl_syntax:syntaxTree()) -> {hm:env(),[hm:constraint()],[hm:predicate()]}.
checkExpr(Env,{match,_,LNode,RNode}) ->
    {Env_, Cons1, Ps} = checkExpr(Env,LNode),
    {LType, Cons2, PsL} = infer(Env_,LNode),
    {RType, Cons3, PsR} = infer(Env,RNode),
    {Env_, Cons1 ++ Cons2 ++ Cons3 ++ [{LType,RType}], Ps ++ PsL ++ PsR};
checkExpr(Env,{var,L,X}) ->
    case env:is_bound(X,Env) of
        true    -> {Env,[],[]};
        false   -> {env:extend(X,hm:fresh(L),Env), [],[]}
    end;
checkExpr(Env,ExprNode) -> 
    {_,Constraints,Ps} = infer(Env, ExprNode),
    {Env,Constraints,Ps}.

% infer the types of patterns in arguments of function definition
-spec inferPatterns(hm:env(),[erl_syntax:syntaxTree()]) -> {[hm:types()],hm:env(),[hm:constraint()],[hm:predicate()]}.
inferPatterns(Env,ClausePatterns) ->
    lists:foldr(
        fun(Pattern,{AccTs,AccEnv,AccCs,AccPs}) ->
            case Pattern of
                {var, L, X} -> 
                    FreshT = hm:fresh(L),
                    AccEnv_ = env:extend(X,FreshT,AccEnv),
                    {[FreshT | AccTs], AccEnv_, AccCs, AccPs};
                _ ->
                    %empty env is used for inference because?
                    {InfT, InfCs, InfPs} = infer(env:empty(),Pattern),
                    {[InfT | AccTs], AccEnv, InfCs ++ AccCs, InfPs ++ AccPs}
            end
        end, {[],Env,[],[]} ,ClausePatterns).

% infer the type of expression on the left of an application
-spec inferFn(hm:env(),erl_syntax:syntaxTree(),integer()) -> {hm:type(),[hm:constraint()],[hm:predicate()]}.
inferFn(Env,{atom,L,X},ArgLen) ->
    {T, Ps} = lookup({X,ArgLen},Env,L), {T,[],Ps};
inferFn(Env,{var,L,X},_) ->
    infer(Env,{var,L,X}).

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

-spec lookup(hm:tvar(),hm:env(),integer()) -> {hm:type(),[hm:predicate()]}.
lookup(X,Env,L) ->
    case env:lookup(X,Env) of
        undefined   -> erlang:error({type_error,util:to_string(X) ++ " not bound on line " ++ util:to_string(L)});
        T           -> hm:freshen(T)
    end.