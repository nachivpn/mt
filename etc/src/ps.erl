-module(ps). % Predicate solver
-import(hm,[
    emptySub/0, comp/2,
    subT/2, subP/2, subPs/2,
    eqType/2,
    unify/2
]).

-export([psMain/2]).

%%%%%%%%%%%%%%%%%%%%%%%%
%% Main predicate solver
%%%%%%%%%%%%%%%%%%%%%%%%

-spec psMain([hm:predicate()],[hm:predicate()]) -> {hm:sub(),[hm:predicate()]}.
psMain(Premise,Ps) ->
    % solve the oc predicates
    {Sub, Unsolved0}    = solveOcPs(Ps),
    % solve class predicates 
    Unsolved1           = solveClassPs(Premise,Unsolved0),
    % select unsolved predicates for generalization
    Unsolved2           = lists:map(fun(P) ->
        case P of
            {class,_,{tvar,_,_}}    -> P;
            {oc,T,[]}               -> erlang:error({type_error, "No matching constructors for " ++ util:to_string(T)});
            {oc,_,_}                -> P;
            _                       -> erlang:error({type_error, "Cannot solve predicate: " ++ util:to_string(P)}) 
        end
    end, Unsolved1),
    {Sub,Unsolved2}.

%%%%%%%%%%%%%%%%%%%%%%%%%
%% Class predicate solver
%%%%%%%%%%%%%%%%%%%%%%%%%

% solves class predicates, and returns unsolveable predicates
% "solving" class predicates is simply weeding out all the preSolved
-spec solveClassPs([hm:predicate()],[hm:predicate()]) -> ([hm:predicate()]).
solveClassPs(Premise,Ps) -> lists:filter(fun(P) -> not preSolved(Premise,P) end, Ps).

% Is the truth of a predicate derivable from the premise?
-spec preSolved([hm:predicate()],hm:predicate()) -> boolean().
preSolved(Premise,{class,C,T}) -> 
    lists:any(fun(P) ->
        case P of
            {class,CX,TX}  -> (C == CX) and eqType(T,TX) ;
            _              -> false
        end
    end, Premise);
preSolved(_,_)        -> false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Overloaded constructor (OC) predicate solver
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-spec solveOcPs([hm:predicate()]) -> {hm:sub(),[hm:predicate()]}.
solveOcPs(Ps) ->
    % solve unification problems in oc predicates
    {Sub0, Unsolved0}    = uniSolveOcPs(emptySub(),Ps),
    % exhaustively search all oc predicates for common substitutions
    Sub1                 = deduceCommonSubst(Unsolved0),
    Unsolved1            = subPs(Unsolved0,Sub1),
    Unsolved2            = reduceOcps(Unsolved1),
    {comp(Sub1,Sub0),Unsolved2}.

% takes a sub and a list of predicates
% returns a sub (obtained by solving predicates) and a list of unsolvable predicates
-spec uniSolveOcPs(hm:sub(),[hm:predicate()]) -> {hm:sub(),[hm:predicate()]}.
uniSolveOcPs(GivenSub,GivenPs) ->
    Reduced = reduceOcps(GivenPs),
    Solveable = lists:any(fun solveableOcP/1, Reduced),
    if
        Solveable -> 
            % fold over the reduced predicates by solving each (solveable) predicate 
            % and accumulating solution and unsolved predicates
            {Sub,Ps} = lists:foldr(fun(P,{AccSub,AccPs}) ->
                % apply accumulated information on predicate to be solved (this may make it un/solvable)
                P_ = subP(P,AccSub),
                case solveOcP(P_) of 
                    % predicate has been solved, 
                    % accumulate subst & apply to accumulated predicates
                    {just, S} -> {comp(S,AccSub),subPs(AccPs,S)};
                    % predicate cannot be solved, add it to unsolved list
                    {nothing} -> {AccSub, [P_|AccPs]}
                end
            end, {GivenSub,[]}, Reduced),
            % this new subst may open up new solveableOcPs
            uniSolveOcPs(Sub,Ps);
        % none of the predicates are solveable
        true -> {GivenSub,Reduced}
    end.

% reduces the ocps by shrinking, simplifying and removing duplicates
-spec reduceOcps([hm:predicate()]) -> [hm:predicate()].
reduceOcps(Ps) -> 
    Ps0 = shrinkCandidates(Ps),
    Ps1 = lists:map(fun simplifyOcp/1, Ps0),
    nubPs(Ps1).

% returns the same number of predicates, only reduces length of candidates
% removes the un-unifiable candidate types
-spec shrinkCandidates([hm:predicate()]) -> [hm:predicate()].
shrinkCandidates(Ps) ->
    lists:map(fun(P) ->
         case P of 
            {oc,CT,MTs}     ->
                % throws away candidates (MTs) that do not unify
                MTs_ = lists:foldr(fun(MT,AccMTs) ->
                    case maybeUnify(MT,CT) of
                        {just,S} -> [subT(MT,S) | AccMTs];
                        {nothing} -> AccMTs
                    end
                end, [], MTs), 
                {oc,CT,MTs_};
            T               -> T
        end
    end, Ps).

% if the constructor arg types and the args of candidates match,
% then the args are thrown away because they will 
% simply unify to yield an empty subtitution
-spec simplifyOcp(hm:predicate()) -> hm:predicate().
simplifyOcp({oc,CT,MTs}=OriginalOcp) ->
    case CT of
        {funt,_,CArgs,CReturnType}  ->
            % if the arguments of the constructor and all candidate types are equal
            EqArgs = lists:all(fun({funt,_,MTArgs,_}) ->
                util:eqLists(fun hm:eqType/2,CArgs,MTArgs)
            end, MTs),
            % then, simply throw the args away and retain only the return types
            case EqArgs of
                true -> 
                    MRTs = lists:map(fun({funt,_,_,ReturnType}) -> ReturnType end,MTs),
                    {oc,CReturnType,MRTs};
                false -> 
                    OriginalOcp
            end;
        _                           ->
            OriginalOcp
    end;
simplifyOcp(X) -> X.

% Is a given OC predicate solveable?
-spec solveableOcP(hm:predicate()) -> boolean().
solveableOcP({oc,_,[_]}) -> true;
solveableOcP(_) -> false.

% Solve an OC predicate: unify the matching type (from singleton solution set) 
% and the constructor's type
-spec solveOcP(hm:predicate()) -> util:maybe(hm:sub()).
solveOcP({oc,CT,[MT]})   -> {just,unify(CT,MT)};
solveOcP(_)              -> {nothing}.

-spec deduceCommonSubst([hm:predicate()]) -> hm:sub().
deduceCommonSubst(Ps) ->
    Subs = deduceCommonSubst(emptySub(),Ps),
    case Subs of
        % none of the branches yielded a unifiable substitution
        [] -> erlang:error({type_error,
            "Unable to unify types of overloaded constructors on lines " 
            ++ util:to_string(getOcpLines(Ps))});
        _ -> intersectSub(Subs)
    end.

% visit every branch caused by a disjunction of unifications 
% in oc predicates and collect common information (substitution)
-spec deduceCommonSubst(hm:sub(),[hm:predicate()]) -> [hm:sub()].
deduceCommonSubst(Sub,[]) -> [Sub];
deduceCommonSubst(Sub,[{oc,_,_}=P|Ps]) -> 
    % apply accumulated information on predicate
    {oc,CT,MTs} = subP(P,Sub),
    % visit every branch
    lists:foldl(fun(MT,AccSubs) -> 
        MaybeS = maybeUnify(CT,MT),
        case MaybeS of
            {just,S} ->
                BranchSubs = deduceCommonSubst(comp(S,Sub),Ps),
                case BranchSubs of
                    % none of the branches returned a solution, all failed
                    [] -> AccSubs; 
                    % atleast oe branch returned a solution, take intersection of them all
                    _ -> [intersectSub(BranchSubs) | AccSubs]
                end;
            {nothing} -> AccSubs
        end
    end,[], MTs);
% no useful information to gain from non-oc predicate
deduceCommonSubst(Sub,[_|Ps]) -> deduceCommonSubst(Sub,Ps).

%%%%%%%%%%%%%
%% Utilities
%%%%%%%%%%%%%

-spec maybeUnify(hm:type(),hm:type()) -> boolean().
maybeUnify(TypeA,TypeB) ->
    try
        unify(TypeA,TypeB)
    of
        S -> {just,S}
    catch
        error:{type_error,_} -> {nothing}
    end.

% remove duplicate occurences of the oc predicate from a list
-spec nubPs([hm:predicate()]) -> [hm:predicate()].
nubPs(Ps) ->
    lists:foldl(fun(P,AccPs) ->
        addToPSet(P,AccPs)
    end,[],Ps).

-spec addToPSet(hm:predicate(),[hm:predicate()]) -> [hm:predicate()].
addToPSet(Px,[P|Ps]=PPs) -> 
    case eqP(Px,P) of
        true    -> PPs;
        false   -> [P|addToPSet(Px,Ps)]
    end;
addToPSet(Px,[]) -> [Px].

-spec eqP(hm:predicate(),hm:predicate()) -> boolean().
eqP({oc,CT1,MTs1},{oc,CT2,MTs2}) -> 
    eqType(CT1,CT2) andalso util:eqLists(fun hm:eqType/2,MTs1,MTs2);
eqP({class,C,T1},{class,C,T2}) ->
    eqType(T1,T2);
eqP(_,_) -> false.

% returns a subtitution which is an intersection of a list of substitutions
-spec intersectSub([hm:sub()]) -> hm:sub().
intersectSub(Ss) -> 
    CommonTVars = util:keysIntersection(Ss),
    TVarTypesList = lists:map(fun(TVar) ->
        Types = lists:map(fun(S) ->
            maps:get(TVar,S)
        end, Ss),
        % a TVar and its types
        {TVar,Types}
    end, sets:to_list(CommonTVars)),
    TVarTypesList_ = lists:filter(
            fun({_,Types}) -> util:allElemEq(fun hm:eqType/2,Types) end, TVarTypesList),
    lists:foldl(fun({TVar,[Type|_]},AccSub) -> 
        maps:put(TVar,Type,AccSub)
    end, maps:new(),TVarTypesList_).

-spec getOcpLines([hm:predicates()]) -> [integer()].
getOcpLines(Ps) ->
    lists:foldl(fun(P,AccLs) ->
        case P of   
            {oc,CT,_} -> [hm:getLn(CT) | AccLs];
            _ -> AccLs
        end
    end,[],Ps).