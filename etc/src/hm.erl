-module(hm).
-export([solve/1,prettyCs/2,prettify/2,emptySub/0,subT/2,freshen/1,generalize/3]).
-export([bt/2,funt/3,tvar/2,forall/4,pretty/1,subE/2,subPs/2,solvePreds/2,fresh/1]).
-export_type([constraint/0,env/0,type/0]).


-type tvar() :: any().
-type env() :: [{tvar(),type()}].
-type sub() :: maps:map(). % Map <tvar(),type()>

-type constraint() :: {type(), type()}.

-type class() :: string().
-type predicate() :: {class(), type()}.

%%%%%%%%%%%%% Type variable constructors

-type type() :: 
    {bt, integer(), type()}
    | {funt, integer(), [type()], type()} 
    | {tvar, integer(), type()}
    | {forall, type(), [predicate()], type()}.

bt (A,L)          -> {bt, L, A}.
funt (A,B,L)      -> {funt, L, A, B}.
tvar (A,L)        -> {tvar, L, A}.
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
unifyMany([],_)             -> erlang:error({type_error, 
                                    "Number of arguments do not match"});
unifyMany(_,[])             -> erlang:error({type_error, 
                                    "Number of arguments do not match"});
unifyMany ([A|As],[B|Bs])   ->
    Sub = unify(A,B),
    As_ = lists:map(fun(T) -> subT(T,Sub) end, As),
    Bs_ = lists:map(fun(T) -> subT(T,Sub) end, Bs),
    comp(unifyMany(As_,Bs_),Sub).

-spec unify(type(), type()) -> sub().
unify ({funt,_,As1, B1}, {funt,_,As2, B2}) -> 
    X = unifyMany (As1, As2),
    Y = unify (subT(B1, X),subT(B2, X)),
    comp(Y,X);
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
    EqLenArgs = length(As1) == (As2),
    case EqLenArgs of
        true -> lists:all(
                    fun(T1,T2) -> eqType(T1,T2) end
                    , lists:zip(As1,As2)) 
                and B1 == B2;
        false -> false
    end;
eqType(_,_) -> false.

%%%%%%%%%%%% Utilities

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
subT ({funt, L, As, B},Sub)   ->
    {funt, L, lists:map(fun(A) -> subT (A,Sub) end, As), subT(B,Sub)};
subT ({forall, {tvar, L, X}, Ps, A}, Sub)   ->
    case maps:is_key(X,Sub) of
        true    ->  {forall, {tvar, L, X}, subPs(Ps,Sub) ,subT(A,maps:remove(X,Sub))};  % avoids name capture!
        false   ->  {forall, {tvar, L, X}, subPs(Ps,Sub) ,subT(A,Sub)}
    end.

% Repetitive substution on a constraint
-spec subC(constraint(), sub()) -> constraint().
subC ({T1,T2},S) -> {subT(T1,S),subT(T2,S)}.

% Repetitive substution on a predicate
-spec subP(predicate(), sub()) -> predicate().
subP ({C,T},S) -> {C,subT(T,S)}.

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
    V == X.

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
free ({forall, {tvar, _, X}, _, A}) 
                        -> sets:del_element(X, free(A)).

-spec freeInEnv(env()) -> set:set(tvar()).
freeInEnv (VTs) ->
    lists:foldr(
            fun sets:union/2,
            sets:new(),
            lists:map(fun({_,T}) -> free(T) end, VTs)).

% converts a mono type to a poly type
-spec generalize(type(),env(),[predicate()]) -> type().
generalize (Type,Env,Ps) ->
    Mono = free (Type),
    BoundInEnv = freeInEnv(Env),
    % Generalizable variables of a type are
    % monotype variables that are not bound in environment
    Generalizable = sets:subtract(Mono, BoundInEnv),
    bindGVs(sets:to_list(Generalizable),Type,Ps).

% bind generalized variables
% TODO: These 0s must be appropriate line numbers of type variables
-spec bindGVs([tvar()],type(),[predicate()]) -> type().
bindGVs ([],T,_)      -> T;
bindGVs ([X|Xs],T,Ps)  -> {forall, {tvar,0, X}, filterPreds(Ps,{tvar,0,X}), bindGVs(Xs,T,Ps)}.

-spec bound(type()) -> [tvar()].
bound ({forall, {tvar, X}, _, A}) -> [X | bound(A)];
bound (_) -> [].

-spec stripbound(type()) -> {type(),[predicate()]}.
stripbound ({forall, {tvar, _,_}, Ps, A}) -> 
    {T,Ps_} = stripbound(A),
    {T,Ps ++ Ps_};
stripbound (T) -> {T,[]}.

% replace all bound variables with fresh variables
-spec freshen (type()) -> {type(), [predicate()]}.
freshen (T) ->
    BoundVars = bound(T),
    % substitution with a fresh variable for every bound variable
    Sub = lists:foldr(
        fun(V, SAcc)->
            comp(SAcc, maps:put(V,env:fresh(),emptySub()))
        end, emptySub(), BoundVars),
    {StrippedT, Ps} = stripbound(T),
    { subT(StrippedT, Sub)
    , subPs(Ps,Sub)}.

%%%%%%%%%%%%%%%%%%%%
%% Predicate solver
%%%%%%%%%%%%%%%%%%%%

-spec filterPreds([predicate()],type()) -> [predicate()].
filterPreds(Ps,T) -> lists:filter(fun({_,X}) -> eqType(T,X) end,Ps).

solved(Given,{C,T}) -> 
    lists:any(fun({CX,TX})-> 
        R = (C == CX) and eqType(T,TX),
        R end, Given).

-spec solvePreds([predicate()],[predicate()]) -> [predicate()].
solvePreds(Given,Ps) -> 
    Filtered = lists:filter(fun(P) -> not solved(Given,P) end, Ps),
    Unsolved = lists:any(
        fun({_,X}) -> case X of {tvar,_,_} -> false; _ -> true end end, Filtered),
    case Unsolved of
        true -> erlang:error({type_error, "Unsolved predicates in " ++ util:to_string(Filtered)});
        false -> Filtered
    end.
    

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
prettify(Env,{forall, T, Ps, A}) ->
    io:fwrite("∀",[]),
    Env_ = prettify(Env, T),
    io:fwrite("[",[]),
    lists:map(fun({C,T_}) -> 
        io:fwrite("~s ",[C]),
        prettify(Env, T_),
        io:fwrite(";",[])
    end, Ps),
    io:fwrite("].",[]),
    prettify(Env_, A).

prettyCs([], S) -> S;
prettyCs([{T1,T2}|Cs],S) -> 
    S_ = prettify(S,T1),
    io:fwrite(" :==: "),
    S__ = prettify(S_,T2),
    io:fwrite("~n"),
    prettyCs(Cs,S__).
