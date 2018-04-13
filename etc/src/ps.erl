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
    {Sub0, Unsolved0}    = solveOcPs(emptySub(),Ps),
    Sub1                 = superSolveOcps(emptySub(),Unsolved0),
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
    {comp(Sub1,Sub0),Unsolved2}.

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

% takes a sub and a list of predicates
% returns a sub (obtained by solving predicates) and a list of unsolvable predicates
-spec solveOcPs(hm:sub(),[hm:predicate()]) -> {hm:sub(),[hm:predicate()]}.
solveOcPs(GivenSub,GivenPs) ->
    Reduced = nubOcPs(shrinkCandidates(GivenPs)),
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
            solveOcPs(Sub,Ps);
        % none of the predicates are solveable
        true -> {GivenSub,Reduced}
    end.

% returns the same number of predicates, only reduces length of candaides
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

% Is a given OC predicate solveable?
-spec solveableOcP(hm:predicate()) -> boolean().
solveableOcP({oc,_,[_]}) -> true;
solveableOcP(_) -> false.

% Solve an OC predicate: unify the matching type (from singleton solution set) 
% and the constructor's type
-spec solveOcP(hm:predicate()) -> util:maybe(hm:sub()).
solveOcP({oc,CT,[MT]})   -> {just,unify(CT,MT)};
solveOcP(_)              -> {nothing}.

-spec nubOcPs([hm:predicate()]) -> [hm:predicate()].
nubOcPs(Ps) ->
    lists:foldl(fun(P,AccPs) ->
        addToOcPSet(P,AccPs)
    end,[],Ps).

-spec superSolveOcps(hm:sub(),[hm:predicate()]) -> hm:sub().
superSolveOcps(Sub,[]) -> Sub;
superSolveOcps(Sub,[{oc,CT,MTs}|Ps]) -> 
    CT_ = subT(CT,Sub),
    Subs = lists:foldl(fun(MT,AccSubs) -> 
        MT_ = subT(MT,Sub),
        MaybeS = maybeUnify(CT_,MT_),
        case MaybeS of
            {just,S} -> [superSolveOcps(comp(S,Sub),Ps) | AccSubs];
            {nothing} -> AccSubs
        end
    end,[], MTs),
    case length(Subs) of
        0 -> erlang:error({type_error,"Unsolvable oc predicate on line " ++ util:to_string(hm:getLn(CT))});
        _ -> intersectSub(Subs)
    end;
superSolveOcps(Sub,[_|Ps]) -> superSolveOcps(Sub,Ps).

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

-spec addToOcPSet(hm:predicate(),[hm:predicate()]) -> [hm:predicate()].
addToOcPSet(Px,[P|Ps]=PPs) -> 
    case eqOcp(Px,P) of
        true    -> PPs;
        false   -> [P|addToOcPSet(Px,Ps)]
    end;
addToOcPSet(Px,[]) -> [Px].

-spec eqOcp(hm:predicate(),hm:predicate()) -> boolean().
eqOcp({oc,CT1,MTs1},{oc,CT2,MTs2}) -> 
    eqType(CT1,CT2) andalso util:eqLists(fun hm:eqType/2,MTs1,MTs2);
eqOcp(_,_) -> false.