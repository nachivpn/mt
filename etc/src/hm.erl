-module(hm).
-export([solve/1,solvePreds/2]).
-export([unify/2]).
-export([emptySub/0,comp/2,subE/2,subT/2,subP/2,subPs/2]).
-export([bt/2,funt/3,tvar/2,tcon/3,forall/4]).
-export([freshen/1,generalize/3,eqType/2,fresh/1]).
-export([getLn/1,pretty/1,prettyCs/2,prettify/2]).
-export_type([constraint/0,env/0,type/0]).


-type tvar() :: any().
-type env() :: [{tvar(),type()}].
-type sub() :: maps:map(). % Map <tvar(),type()>

-type constraint() :: {type(), type()}.

-type class() :: string().
-type predicate() :: {class, class(), type()} | {oc, type(),[type()]}.

%%%%%%%%%%%%% Type variable constructors

-type type() :: 
    {bt, integer(), type()}
    | {funt, integer(), [type()], type()} 
    | {tvar, integer(), type()}
    | {tcon, integer(), string(),[type()]}
    | {forall, type(), [predicate()], type()}
    | {whilst, [predicate()], type()}.

bt (A,L)          -> {bt, L, A}.
funt (A,B,L)      -> {funt, L, A, B}.
tvar (A,L)        -> {tvar, L, A}.
tcon(N,A,L)       -> {tcon, L, N, A}.
forall (X,P,A,L)  -> {forall, tvar(X,L), P, A}.

%%%%%%%%%%%% Constraint solver

-spec solve([constraint()]) -> sub().
solve(Cs) -> solve(Cs, emptySub()).

-spec solve([constraint()], sub()) -> sub().
solve ([],Sub) -> Sub;
solve ([{T1,T2}|Cs],Sub) ->
    Sub_ = unify(T1,T2),
    solve(
        % apply new substitution to remaining constraints
        lists:map(fun(Cx) -> subC(Cx, Sub_) end, Cs), 
        % compose substitutions
        comp(Sub_,Sub)).

%%%%%%%%%%%% Unification algorithm

-spec unifyMany([type()],[type()]) -> sub().
unifyMany([],[])            -> emptySub();
unifyMany([],_)             -> erlang:error({type_error, "arg_mismatch"});
unifyMany(_,[])             -> erlang:error({type_error, "arg_mismatch"});
unifyMany ([A|As],[B|Bs])   ->
    Sub = unify(A,B),
    As_ = lists:map(fun(T) -> subT(T,Sub) end, As),
    Bs_ = lists:map(fun(T) -> subT(T,Sub) end, Bs),
    comp(unifyMany(As_,Bs_),Sub).

% unify is left biased (this is a crucial property relied upon!)
% i.e., unify(T1,T2) returns substitution for T1 in terms of T2
-spec unify(type(), type()) -> sub().
unify ({funt,L1,As1, B1}, {funt,L2,As2, B2}) ->
    try
        unifyMany (As1, As2)
    of
        X -> 
            Y = unify (subT(B1, X),subT(B2, X)),
            comp(Y,X)
    catch
        error:{type_error,"arg_mismatch"} -> erlang:error({type_error, 
                                    "Number of arguments to function on line " ++ util:to_string(L1) ++ " do not match"
                                    ++ " arguments on line " ++ util:to_string(L2)})
    end;  
unify ({tvar,L,V},T) ->
    Eq  = eqType({tvar, L,V}, T),
    Occ = occurs(V,T),
    if
        Eq              -> emptySub();
        Occ             -> erlang:error({type_error,
                                "Failed occurs check on line" ++ util:to_string(L)});
        true            -> maps:put(V,T,emptySub())
    end;
unify (T,{tvar,L,V}) ->
    unify ({tvar,L,V},T);
unify({tcon,L1,N1,As1},{tcon,L2,N2,As2}) ->
    case N1 == N2 of
        true        -> 
            try
                unifyMany(As1,As2)
            catch   
                error:{type_error,"arg_mismatch"} -> erlang:error({type_error, 
                                    "Number of arguments to type constructor on line " ++ util:to_string(L1) ++ " do not match"
                                    ++ " arguments on line " ++ util:to_string(L2)})
            end;
        false       -> erlang:error({type_error,
                        "Cannot unify "++ util:to_string(N1) 
                        ++ " (on line "++ util:to_string(L1) ++")"
                        ++" with " ++ util:to_string(N2) 
                        ++ " (on line "++ util:to_string(L2) ++")"})
    end;
unify (T,U) ->
    Eq = eqType(T,U),
    if
        Eq          -> emptySub();
        true        -> erlang:error({type_error, 
                            "Cannot unify " ++ util:to_string(T) ++ 
                            " with " ++ util:to_string(U)})
    end.

-spec eqType(type(),type()) -> boolean().
eqType({bt,_,A}, {bt,_,B}) -> A == B;
eqType({tvar,_,X}, {tvar,_,Y}) -> X == Y;
eqType({funt,_,As1, B1}, {funt,_,As2, B2}) ->
    EqLenArgs = length(As1) == length(As2),
    case EqLenArgs of
        true -> lists:all(
                    fun({T1,T2}) -> eqType(T1,T2) end
                    , lists:zip(As1,As2)) 
                and (B1 == B2);
        false -> false
    end;
eqType({tcon,_,N1,As1},{tcon,_,N2,As2}) ->
    case (N1 == N2) and (length(As1) == length(As2)) of
        true -> lists:all(
                    fun(T1,T2) -> eqType(T1,T2) end
                    , lists:zip(As1,As2));
        false -> false
    end;
eqType(_,_) -> false.

%%%%%%%%%%%% Utilities

-spec getLn(type()) -> integer().
getLn ({bt, L, _})          -> L;
getLn ({funt, L, _, _})     -> L;
getLn ({tvar, L, _})        -> L;
getLn ({tcon, L, _, _})    -> L;
getLn ({forall, {tvar, L, _}, _, _}) -> L;
getLn ({whilst, _, T}) -> getLn(T).


-spec fresh(integer()) -> type().
fresh(L) -> tvar(make_ref(),L).

-spec emptySub() -> sub().
emptySub () -> maps:new().

% Compose two substitutions
-spec comp(sub(), sub()) -> sub().
comp (X,Y) ->
    Y_ = maps:map( % apply subtitution X on every entry in Y
            fun(_,Type) -> subT(Type,X) end, Y),
    maps:merge(X,Y_).   % union (Y_, entries in X whose keys are not in Y)

% Apply a subtitution to a type
-spec subT(type(), sub()) -> type().
subT ({tvar, L, X}, Sub)  ->
    case maps:is_key(X,Sub) of
        true    ->  maps:get(X,Sub);
        false   ->  {tvar, L, X}
    end;
subT ({bt, L, T}, _)  ->
    {bt, L, T};
subT ({funt, L, As, B}, Sub)   ->
    {funt, L, lists:map(fun(A) -> subT (A,Sub) end, As), subT(B,Sub)};
subT ({tcon, L, N, As}, Sub)   ->
    {tcon, L, N, lists:map(fun(A) -> subT (A,Sub) end, As)};
subT ({forall, {tvar, L, X}, Ps, A}, Sub)   ->
    case maps:is_key(X,Sub) of
        true    ->  {forall, {tvar, L, X}, subPs(Ps,Sub) ,subT(A,maps:remove(X,Sub))};  % avoids name capture!
        false   ->  {forall, {tvar, L, X}, subPs(Ps,Sub) ,subT(A,Sub)}
    end;
subT ({whilst,Ps,T},Sub) -> {whilst,subPs(Ps,Sub),subT(T,Sub)}.

% Repetitive substution on a constraint
-spec subC(constraint(), sub()) -> constraint().
subC ({T1,T2},S) -> {subT(T1,S),subT(T2,S)}.

% Repetitive substution on a predicate
-spec subP(predicate(), sub()) -> predicate().
subP ({class,C,T},S) -> {class,C,subT(T,S)};
subP ({oc,T,MatcingTypes},S) -> 
    {oc, subT(T,S), lists:map(fun(MT)-> subT(MT,S) end, MatcingTypes)}.

% Repetitive substution on a predicate
-spec subPs([predicate()], sub()) -> predicate().
subPs (Ps,S) -> lists:map(fun(P) -> subP(P,S) end, Ps).

% Repetitive substution on a environment
-spec subE(env(), sub()) -> env().
subE (Env,S) -> env:mapV(fun(T) -> subT(T,S) end, Env).

-spec occurs(tvar(), type()) -> boolean().
occurs (V,{funt, _, As, B}) ->
    lists:any(fun(A) -> occurs(V,A) end, As) or occurs(V,B);
occurs (_,{bt,_,_}) ->
    false;
occurs (V,{tvar,_, X}) ->
    V == X;
occurs (V,{tcon,_,_,As}) ->
    lists:any(fun(A) -> occurs(V,A) end, As).

% All free type variables in the given type
-spec free(type()) -> set:set(tvar()).
free ({bt, _, _})          -> sets:new();
free ({funt, _, As, B})     -> 
    sets:union(
        lists:foldr(
            fun(A, AccSet) -> sets:union(free(A),AccSet) end
            , sets:new(), As)
        , free (B));
free ({tvar, _, A})        -> sets:add_element(A,sets:new());
free ({tcon, _, _, As})    -> 
    lists:foldr(
        fun(A, AccSet) -> sets:union(free(A),AccSet) end
    , sets:new(), As);
free ({forall, {tvar, _, X}, _, A}) 
                        -> sets:del_element(X, free(A));
free ({whilst,_,T})         -> free(T).

-spec freeInEnv(env()) -> set:set(tvar()).
freeInEnv (VTs) ->
    lists:foldr(
            fun sets:union/2,
            sets:new(),
            lists:map(fun({_,T}) -> free(T) end, VTs)).

-spec freeInPs([predicate()]) -> set:set(tvar()).
freeInPs(Ps) ->
    lists:foldl(fun(P,AccFree)-> 
            case P of 
                {oc,CT,MTs}   -> 
                    Free = lists:foldl(fun(MT,AccFree_) -> 
                        sets:union(AccFree_,free(MT))
                    end, free(CT), MTs),
                    sets:union(AccFree,Free);
                {class,_,T}   -> sets:union(AccFree,free(T))
            end
        end, sets:new(), Ps).

% converts a mono type to a poly type
-spec generalize(type(),env(),[predicate()]) -> type().
generalize (Type,Env,Ps) ->
    MonoVars = sets:union(free(Type),freeInPs(Ps)),
    BoundInEnv = freeInEnv(Env),
    % Generalizable variables of a type are
    % monotype variables that are not bound in environment
    Generalizable = sets:subtract(MonoVars, BoundInEnv),
    bindGVs(sets:to_list(Generalizable),Type,Ps).

% bind generalized variables
-spec bindGVs([tvar()],type(),[predicate()]) -> type().
bindGVs ([],T,Ps)      -> {whilst, getUniPreds(Ps),T};
bindGVs ([X|Xs],T,Ps)  -> {forall, {tvar,getLn(T), X}, getClassPredsOn(Ps,{tvar,getLn(T),X}), bindGVs(Xs,T,Ps)}.

-spec bound(type()) -> [{tvar(),integer()}].
bound ({forall, {tvar,L,X},_, A}) -> [{X,L} | bound(A)];
bound (_) -> [].

-spec stripbound(type()) -> {type(),[predicate()]}.
stripbound ({forall, {tvar, _,_}, Ps, A}) -> 
    {T,Ps_} = stripbound(A),
    {T,Ps ++ Ps_};
stripbound ({whilst,UPs,T}) -> {T,UPs};
stripbound (T) -> {T,[]}.

% replace all bound variables with fresh variables
-spec freshen (type()) -> {type(), [predicate()]}.
freshen (T) ->
    BoundVars = bound(T),
    % substitution with a fresh variable for every bound variable
    Sub = lists:foldr(
        fun({V,L}, SAcc)->
            comp(SAcc, maps:put(V,hm:fresh(L),emptySub()))
        end, emptySub(), BoundVars),
    {StrippedT, Ps} = stripbound(T),
    { subT(StrippedT, Sub)
    , subPs(Ps,Sub)}.

% get predicates on a certain type
-spec getClassPredsOn([predicate()],type()) -> [predicate()].
getClassPredsOn(Ps,T) -> 
    lists:filter(fun(P) ->
        case P of
            {class,_,X} -> eqType(T,X);
            _           -> false
        end
    end,Ps).

% get all unification predicates
-spec getUniPreds([predicate()]) -> [predicate()].
getUniPreds(Ps) -> 
    lists:filter(fun(P) ->
        case P of
            {oc,_,_} -> true;
            _           -> false
        end
    end,Ps).

% Predicate solver (proxy)
-spec solvePreds([predicate()],[predicate()]) -> {sub(),[predicate()]}.
solvePreds(Premise,Ps) -> ps:psMain(Premise,Ps).

%%%%%%%%%%%%%%%%%%%%
%% Pretty printing
%%%%%%%%%%%%%%%%%%%%
% pretty :: Type -> IO
pretty(T) -> 
    prettify([],T),
    ok.

% Stateful pretty printer
prettify(Env, {bt, _, A}) -> io:fwrite("~p", [A]), Env;
prettify(Env, {funt, _, As, B}) ->
    io:fwrite("(", []),
    Env_ = util:interFoldEffect(
        fun(A,E) -> prettify(E,A) end
        , fun() -> io:fwrite(",") end
        , Env, As),
    io:fwrite(")", []),
    io:fwrite("->", []),
    Env__ = prettify(Env_,B),
    Env__;
prettify(Env, {tvar, _, A}) ->
    X = env:lookup(A, Env),
    case X of
        undefined -> 
            L = length(Env) + 65,
            io:fwrite("~c", [L]),
            env:extend(A,L,Env);       
        _         -> 
            io:fwrite("~c", [X]),
            Env
    end;
prettify(Env, {tcon, _, N, As}) ->
    io:fwrite("~s ", [N]),
    util:interFoldEffect(
        fun(A,E) -> prettify(E,A) end
        , fun() -> io:fwrite(" ") end
        , Env, As);
prettify(Env,{forall, T, Ps, A}) ->
    io:fwrite("∀",[]),
    Env1 = prettify(Env, T),
    io:fwrite("[",[]),
    Env2 = lists:foldl(fun(P, AccEnv) ->
        case P of
            {class,C,T_} -> 
                io:fwrite("~s ",[C]),
                AccEnv_ = prettify(AccEnv, T_),
                io:fwrite(";",[]),
                AccEnv_
        end
    end, Env1, Ps),
    io:fwrite("].",[]),
    prettify(Env2, A);
prettify(Env,{whilst,Ps,A}) ->
    Env1 = lists:foldl(fun(P, AccEnv) ->
        case P of
            {oc,CT,MTs} ->
                AccEnv_ = prettify(AccEnv, CT),
                io:fwrite(" :~~: {",[]),
                AccEnv__ = util:interFoldEffect(
                    fun(MT,AccE) -> prettify(AccE,MT) end
                    ,fun() -> io:fwrite(" || ") end
                , AccEnv_, MTs),
                io:fwrite("} ",[]),
                AccEnv__
        end
    end, Env, Ps),
    prettify(Env1, A).


prettyCs([], S) -> S;
prettyCs([{T1,T2}|Cs],S) -> 
    S_ = prettify(S,T1),
    io:fwrite(" :==: "),
    S__ = prettify(S_,T2),
    io:fwrite("~n"),
    prettyCs(Cs,S__).
