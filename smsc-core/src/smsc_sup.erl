%%%-------------------------------------------------------------------
%%% @doc
%%% SMSC Core Supervisor
%%% @end
%%%-------------------------------------------------------------------
-module(smsc_sup).
-behaviour(supervisor).

%% API
-export([start_link/0]).

%% Supervisor callbacks
-export([init/1]).

-define(SERVER, ?MODULE).

%%====================================================================
%% API functions
%%====================================================================

start_link() ->
    io:format("Starting SMSC supervisor link...~n"),
    supervisor:start_link({local, ?SERVER}, ?MODULE, []).

%%====================================================================
%% Supervisor callbacks
%%====================================================================

init([]) ->
    io:format("Initializing SMSC supervisor...~n"),
    
    SupFlags = #{strategy => one_for_one,
                 intensity => 10,
                 period => 5},
    
    SmscServer = #{
        id => smsc_server,
        start => {smsc_server, start_link, []},
        restart => permanent,
        shutdown => 5000,
        type => worker,
        modules => [smsc_server]
    },
    
    io:format("Starting supervisor with SMSC server~n"),
    {ok, {SupFlags, [SmscServer]}}.
