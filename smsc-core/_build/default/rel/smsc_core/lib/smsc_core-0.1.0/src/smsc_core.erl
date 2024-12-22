%%%-------------------------------------------------------------------
%%% @doc
%%% SMSC Core Application
%%% @end
%%%-------------------------------------------------------------------
-module(smsc_core).

-behaviour(application).

%% Application callbacks
-export([start/2, stop/1]).

%% API exports
-export([submit_message/1, query_message/1, cancel_message/1]).
-export([get_metrics/0, update_config/2, get_config/1]).

%%%====================================================================
%%% API functions
%%%====================================================================

submit_message(Params) ->
    gen_server:call(smsc_server, {submit_message, Params}).

query_message(MessageId) ->
    gen_server:call(smsc_server, {query_message, MessageId}).

cancel_message(MessageId) ->
    gen_server:call(smsc_server, {cancel_message, MessageId}).

get_metrics() ->
    gen_server:call(smsc_server, get_metrics).

update_config(Section, Config) ->
    io:format("Core: Updating config for section ~p with: ~p~n", [Section, Config]),
    try
        Result = gen_server:call(smsc_server, {update_config, Section, Config}),
        io:format("Core: Update result: ~p~n", [Result]),
        case Result of
            {error, _} = Error -> Error;
            Config when is_map(Config) -> {ok, Config}
        end
    catch
        Type:Error:Stack ->
            io:format("Core: Error updating config:~nType: ~p~nError: ~p~nStack: ~p~n", 
                     [Type, Error, Stack]),
            {error, {Type, Error}}
    end.

get_config(Section) ->
    io:format("Core: Getting config for section ~p~n", [Section]),
    try
        Result = gen_server:call(smsc_server, {get_config, Section}),
        io:format("Core: Got config result: ~p~n", [Result]),
        Result
    catch
        Type:Error:Stack ->
            io:format("Core: Error getting config:~nType: ~p~nError: ~p~nStack: ~p~n", 
                     [Type, Error, Stack]),
            {error, {Type, Error}}
    end.

%%%====================================================================
%%% Application callbacks
%%%====================================================================

start(_StartType, _StartArgs) ->
    % Initialize the database first
    case smsc_db:init() of
        ok ->
            io:format("Core: Database initialized successfully~n"),
            % Then start the supervisor
            case smsc_sup:start_link() of
                {ok, Pid} ->
                    {ok, Pid};
                Error ->
                    io:format("Core: Failed to start supervisor: ~p~n", [Error]),
                    Error
            end;
        Error ->
            io:format("Core: Database initialization failed: ~p~n", [Error]),
            Error
    end.

stop(_State) ->
    ok.
