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
    % get all user define data types (UDTs) 
    UDTs = lists:filter(fun (Node) -> 
            (type(Node) == 'attribute') andalso
            (element(3,Node) == 'type')
    end, Forms),
    % add UDTs to default env
    Env = lists:foldl(fun(UDT,AccEnv) -> 
        addUDTNode(UDT,AccEnv) 
    end, rt:defaultEnv(), UDTs),
    % get all functions
    Functions = lists:filter(
        fun (Node) -> type(Node) == function end, Forms),
    % make strongly connected components (SCCs) (sorted in topological ordering)
    SCCs = da:mkSCCs(Functions),
    % type check each SCC and exend Env
    try
        lists:foldl(fun(SCC, AccEnv) ->
               typeCheckSCC(SCC,AccEnv)
        end, Env, SCCs)
    of  
        Env_ -> 
            lists:map(fun({X,T}) -> 
                io:fwrite("~p :: ",[X]), 
                hm:pretty(T), 
                io:fwrite("~n",[])
            end, lists:reverse(Env_))
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
            ClauseGaurds = clause_guard(Node),
            {CsGaurds, PsGaurds} = checkGaurds(Env_,ClauseGaurds),
            Body = clause_body(Node),
            {Env__, CsBody, PsBody} =lists:foldl(
                fun(Expr, {Ei,Csi,Psi}) -> 
                    {Ei_,Csi_,Psi_} = checkExpr(Ei,Expr),
                    {Ei_, Csi ++ Csi_, Psi ++ Psi_}
                end, {Env_,[],[]}, lists:droplast(Body)),
            {ReturnType, CsLast, PsLast} = infer(Env__, lists:last(Body)),
            {hm:funt(ArgTypes,ReturnType,L)
            , CsArgs ++ CsGaurds ++ CsBody ++ CsLast 
            , PsArgs ++ PsGaurds ++ PsBody ++ PsLast};
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
            {hm:tcon("List",[hm:fresh(L)],L),[],[]};
        list -> 
            {cons,L,H,T} = Node,
            {HType,HCs,HPs} = infer(Env, H),
            {TType,TCs,TPs} = infer(Env, T),
            % generate a fresh "List V"
            V = hm:fresh(L), 
            LType = {tcon, L, "List", [V]},
            {LType, HCs ++ TCs ++ 
                unify(HType,V) ++   % unify head type with "V" 
                unify(TType,LType)  % unify tail type with "List V"
            , HPs ++ TPs};
        tuple ->
            {tuple,L,Es} = Node,
            [HeadEl|TailEls] = Es,
            case type(HeadEl) of
                % if first element of tuple is an atom,
                atom        ->
                    % then consider it as a constructor
                    {atom,L,Constructor} = HeadEl,
                    % and the tail as arguments to constructor
                    Args = TailEls,
                    {ConstrType,ConstrPs}   = lookup(Constructor,Env,L),
                    {ArgTypes,ArgCs,ArgPs}  = lists:foldl(fun(X, {AccT,AccCs,AccPs}) -> 
                        {T,Cs,Ps} = infer(Env,X),
                        {AccT ++ [T], AccCs ++ Cs, AccPs ++ Ps}
                    end, {[],[],[]}, Args),
                    V = hm:fresh(L),
                    {V, ArgCs ++ unify(ConstrType, hm:funt(ArgTypes,V,L)), ConstrPs ++ ArgPs};
                _           ->
                    {Ts,Cs,Ps} = lists:foldl(
                        fun(X, {AccT,AccCs,AccPs}) -> 
                            {T,Cs,Ps} = infer(Env,X),
                            {AccT ++ [T], AccCs ++ Cs, AccPs ++ Ps}
                        end, {[],[],[]}, Es),
                    {hm:tcon("Tuple",Ts,L),Cs,Ps}
            end;
        underscore ->
            {var,L,'_'} = Node,
            {hm:fresh(L),[],[]};
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
checkExpr(Env,{tuple,_,Es}) ->
    lists:foldl(fun(E, {AccEnv,AccCs,AccPs}) ->
        {ChEnv,ChCs,ChPs} = checkExpr(AccEnv,E),
        {ChEnv, AccCs ++ ChCs, AccPs ++ ChPs}
    end, {Env,[],[]}, Es);
checkExpr(Env,{cons,_,H,T}) ->
    {Env_,HCs,HPs} = checkExpr(Env,H),
    {Env__,TCs,TPs} = checkExpr(Env_,T),
    {Env__,HCs ++ TCs, HPs ++ TPs};
checkExpr(Env,ExprNode) -> 
    {_,Constraints,Ps} = infer(Env, ExprNode),
    {Env,Constraints,Ps}.

% infer the types of patterns in arguments of function definition
-spec inferPatterns(hm:env(),[erl_syntax:syntaxTree()]) -> {[hm:types()],hm:env(),[hm:constraint()],[hm:predicate()]}.
inferPatterns(Env,ClausePatterns) ->
    lists:foldl(
        fun(Pattern,{AccTs,AccEnv,AccCs,AccPs}) ->
            % checkExpr takes care of extending the env w/ variables in a pattern
            {Env_, ChCs, ChPs} = checkExpr(AccEnv,Pattern),
            {InfT, InfCs, InfPs} = infer(Env_,Pattern),
            {AccTs ++ [InfT], Env_, AccCs ++ ChCs ++ InfCs, AccPs ++ ChPs ++ InfPs }
        end, {[],Env,[],[]} ,ClausePatterns).

% infer the type of expression on the left of an application
-spec inferFn(hm:env(),erl_syntax:syntaxTree(),integer()) -> {hm:type(),[hm:constraint()],[hm:predicate()]}.
inferFn(Env,{atom,L,X},ArgLen) ->
    {T, Ps} = lookup({X,ArgLen},Env,L), {T,[],Ps};
inferFn(Env,{var,L,X},_) ->
    infer(Env,{var,L,X}).

-spec checkGaurds(hm:env(),erl_syntax:syntaxTree()) -> {[hm:constraint()],[hm:predicate()]}.
checkGaurds(Env,{tree,disjunction,_,Conjuctions}) ->
    lists:foldr(fun({tree,conjunction,_,Exprs}, {DAccCs, DAccPs}) ->
        {Cs,Ps} = lists:foldr(fun(Expr,{CAccCs,CAccPs}) -> 
            {InfT,InfCs,InfPs} = infer(Env,Expr),
            {unify(InfT,hm:bt(boolean,0)) ++ InfCs ++ CAccCs, InfPs ++ CAccPs} 
        end, {[],[]}, Exprs),
        {Cs ++ DAccCs, Ps ++ DAccPs}
   end, {[],[]}, Conjuctions);
checkGaurds(_,none) -> {[],[]}.

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


-spec addUDTNode(hm:env(),erl_syntax:syntaxTree()) -> hm:env().
addUDTNode(Node,Env) ->
    addUDT(element(4,Node),Env,util:getLn(Node)).    

-spec addUDT(hm:env(),erl_syntax:syntaxTree(),integer()) -> hm:env().
addUDT({TypeConstr,DataConstrs,Args},Env,L) ->
    % make type constructor
    Type = hm:tcon(TypeConstr,lists:map(fun node2type/1, Args),L),
    % add every data constructor to Env
    lists:foldl(fun({DConstr,DConstrType}, AccEnv) ->
        PolyDConstrType = hm:generalize(DConstrType,Env,[]),
        env:extend(DConstr,PolyDConstrType,AccEnv)
    end, Env, getConstrTypes(Type, DataConstrs)). 

% returns a list of Env entries - one for each data constructor
-spec getConstrTypes(hm:type(),erl_syntax:syntaxTree()) -> [{var(),hm:type()}].
getConstrTypes(Type,{type,L,tuple,[{atom,_,DataConstr}|Args]}) ->
    ArgTypes = lists:map(fun node2type/1, Args),
    [{DataConstr,hm:funt(ArgTypes,Type,L)}];
getConstrTypes(Type,{type,_,union,DataConstrDefns}) -> 
    lists:concat(
        lists:map(
            fun(DCD) -> getConstrTypes(Type,DCD) end, DataConstrDefns)).

% converts a type (node) in the AST to a hm:type()
-spec node2type(erl_syntax:syntaxTree()) -> hm:type().
node2type({var,L,X}) -> hm:tvar(X,L);
node2type({user_type,L,T,Args}) -> hm:tcon(T,lists:map(fun node2type/1, Args),L).


