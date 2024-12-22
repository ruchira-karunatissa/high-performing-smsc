%%%-------------------------------------------------------------------
%%% @doc
%%% SMSC Utility Functions
%%% @end
%%%-------------------------------------------------------------------
-module(smsc_utils).

-export([restart_http/0, restart/0]).

restart() ->
    io:format("~n=== Restarting SMSC Application ===~n"),
    
    % Stop all applications
    io:format("Stopping applications...~n"),
    [begin
        io:format("Stopping ~p...~n", [App]),
        application:stop(App)
    end || App <- [smsc_core, cowboy, ranch, crypto, asn1, public_key, ssl]],
    
    timer:sleep(1000),  % Give some time for everything to stop
    
    % Start all applications
    io:format("Starting applications...~n"),
    case application:ensure_all_started(smsc_core) of
        {ok, Started} ->
            io:format("Started applications: ~p~n", [Started]),
            % Set up HTTP server
            case setup_http_server() of
                ok -> 
                    io:format("HTTP server started successfully~n"),
                    ok;
                {error, Reason} ->
                    io:format("Failed to start HTTP server: ~p~n", [Reason]),
                    {error, Reason}
            end;
        {error, {App, Reason}} ->
            io:format("Failed to start ~p: ~p~n", [App, Reason]),
            {error, {App, Reason}}
    end.

setup_http_server() ->
    io:format("Setting up HTTP server...~n"),
    Port = application:get_env(smsc_core, http_port, 8080),
    io:format("Using port: ~p~n", [Port]),
    
    % First stop any existing listener
    io:format("Stopping existing HTTP listener...~n"),
    case cowboy:stop_listener(http_listener) of
        ok -> io:format("Existing listener stopped~n");
        {error, not_found} -> io:format("No existing listener found~n");
        Error -> io:format("Error stopping listener: ~p~n", [Error])
    end,
    
    % Set up routes
    Dispatch = cowboy_router:compile([
        {'_', [
            {"/api/messages", smsc_http_handler, []},
            {"/api/messages/:id", smsc_http_handler, []},
            {"/api/metrics", smsc_http_handler, []},
            {"/api/config", smsc_http_handler, []}
        ]}
    ]),
    io:format("Routes configured: ~p~n", [Dispatch]),
    
    % Start the listener
    case cowboy:start_clear(http_listener,
        [{port, Port}],
        #{env => #{dispatch => Dispatch}}) of
        {ok, _} -> 
            io:format("HTTP server started successfully on port ~p~n", [Port]),
            ok;
        {error, Reason} ->
            io:format("Failed to start HTTP server: ~p~n", [Reason]),
            {error, Reason}
    end.

restart_http() ->
    io:format("Use smsc_utils:restart() instead for a complete restart~n"),
    setup_http_server().
