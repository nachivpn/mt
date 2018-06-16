-module(ft_worker_pool).
-compile(export_all).

%%
%% worker_pool([Fun]) -> [Results]
worker_pool(Funs) -> 
    Nodes = [node() | nodes()],
    Master = self(),
    Workers = lists:flatten([initNode(Node,Master,10) || Node <- Nodes]),
    process_flag(trap_exit, true),
    master(Funs,[],Workers,[]).

-type master(A,R) :: {work_response,A,pid()} | {get_work,pid()} | {'EXIT',Pid,A}.

flushDead(Pid) -> 
    receive 
        {work_response,_,Pid} -> flushDead(Pid);
        {get_work,Pid} -> flushDead(Pid)
        % after 0 -> ok 
    end.

%%
%% start processess on the nodes, and return their pids
%% 
initNode(Node,Master,WorkerSize) -> [spawn_worker(Node,Master) || _ <- lists:seq(1,WorkerSize)].

%% Master node first attempts to spawn all the available work on available workers
%% When it runs out of available workers, 
%% it waits for a running worker to return (and hence free up) and schedules on it
%% Once, all the work has been dispatched, it simply reads all the remaining results
%% While reading the results from mailbox, if it finds that some worker crased, 
%% it simply flushes all messages form worker (required as we don't read in order) 
%% and re-schedules the failed task. It uses a task registry [{Task, Worker}] to achieve this

% no work, busy jobs or live workers
master([],[],[],Results) -> Results;
% no work or busy jobs, shut down workers
master([],[],Workers,Results) -> 
    [ receive 
        {get_work,W} -> 
            W ! {no_work,normal},
            receive
                {'EXIT',W,normal} -> ok
            end
        end 
        || W<-Workers],
    master([],[],[],Results);
% no work left to dispatch, read all responses
master([],WReg,Workers,Results) ->
    receive
        {work_response,Result,Pid} ->
            ResultsN = [Result|Results],
            CompletedJob = proplists:lookup(Pid,WReg),
            WRegN = lists:delete(CompletedJob,WReg),
            IsLiveWorker = lists:member(Pid,Workers),
            WorkersN = if IsLiveWorker -> Workers; true -> [Pid | Workers] end, 
            master([],WRegN,WorkersN,ResultsN);
        {'EXIT',Pid,_} ->
            IsPoolWorker = lists:member(Pid,Workers) or lists:member(Pid,proplists:get_keys(WReg)),
            if 
                IsPoolWorker -> 
                    IncompleteWs = proplists:get_all_values(Pid,WReg),
                    WRegN = proplists:delete(Pid,WReg),
                    WorkersN = lists:delete(Pid,Workers),
                    flushDead(Pid),
                    master(IncompleteWs,WRegN,WorkersN,Results);
                true -> master([],WReg,Workers,Results) 
            end

    end;
%%no workers left, read one response and make worker available
master(Ws,WReg,[],Results) ->
    receive
        {work_response,Result,Pid} ->
            ResultsN = [Result|Results],
            CompletedJob = proplists:lookup(Pid,WReg),
            WRegN = lists:delete(CompletedJob,WReg),
            master(Ws,WRegN,[Pid],ResultsN)
    end;
%% dispatch work on a worker asking for it
master([W|Ws],WReg,Workers,Results) ->
    receive
        {get_work,Pid} -> 
            Pid ! {new_work,W},
            WRegN = [{Pid,W}|WReg],
            WorkersN = lists:delete(Pid,Workers),
            master(Ws,WRegN,WorkersN,Results)
    end.

%%
%% Worker
%%
worker(Master) ->
    Master ! {get_work, self()},
    receive
        {new_work,W} -> 
            Master ! {work_response,W(),self()}, 
            worker(Master);
        {no_work,Reason} -> exit(Reason)
    end.

%%
%% spawn_worker(Node) -> worker_pid
%%
spawn_worker(Node,Master) -> spawn_link(Node, fun() -> worker(Master) end).
