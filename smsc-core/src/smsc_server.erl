%%%-------------------------------------------------------------------
%%% @doc
%%% SMSC Server Implementation
%%% @end
%%%-------------------------------------------------------------------
-module(smsc_server).
-behaviour(gen_server).

%% Include required libraries
-include_lib("kernel/include/logger.hrl").

%% API exports
-export([start_link/0]).

%% gen_server callbacks
-export([init/1, handle_call/3, handle_cast/2, handle_info/2,
         terminate/2, code_change/3]).

%%%===================================================================
%%% Record Definitions
%%%===================================================================

-record(state, {
    messages = #{} :: map(),
    metrics = #{
        total_messages => 0,
        successful_messages => 0,
        failed_messages => 0,
        messages_per_second => 0,
        recent_messages => []
    } :: map(),
    last_metrics_update = erlang:system_time(second) :: integer(),
    config = undefined :: undefined | map()
}).

-record(message, {
    id :: binary(),
    content :: binary(),
    priority :: integer(),
    status :: atom(),
    timestamp :: integer(),
    retries = 0 :: integer()
}).

%%%===================================================================
%%% API
%%%===================================================================

start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

%%%===================================================================
%%% gen_server callbacks
%%%===================================================================

init([]) ->
    process_flag(trap_exit, true),
    % Initialize database
    ok = smsc_db:init(),
    % Load initial configuration
    InitialConfig = case smsc_db:get_config(<<"smsc_config">>) of
        {ok, Config} -> Config;
        {error, _} -> undefined
    end,
    % Initialize metrics timer
    erlang:send_after(1000, self(), update_metrics),
    % Initialize state with loaded config
    {ok, #state{config = InitialConfig}}.

handle_call({submit_message, Params}, _From, State) ->
    MessageId = generate_message_id(),
    Message = #message{
        id = MessageId,
        content = maps:get(<<"content">>, Params),
        priority = maps:get(<<"priority">>, Params, 1),
        status = pending,
        timestamp = erlang:system_time(second)
    },
    
    % Save to database
    ok = smsc_db:save_message(#{
        id => Message#message.id,
        content => Message#message.content,
        priority => Message#message.priority,
        status => Message#message.status
    }),
    
    NewMetrics = maps:update_with(
        total_messages,
        fun(V) -> V + 1 end,
        1,
        State#state.metrics
    ),
    
    NewState = State#state{
        messages = maps:put(MessageId, Message, State#state.messages),
        metrics = update_metrics_for_new_message(NewMetrics, Message)
    },
    
    {reply, {ok, MessageId}, NewState};

handle_call({query_message, MessageId}, _From, State) ->
    case smsc_db:get_message(MessageId) of
        {ok, Message} ->
            {reply, {ok, Message}, State};
        {error, _} = Error ->
            {reply, Error, State}
    end;

handle_call({cancel_message, MessageId}, _From, State) ->
    case smsc_db:update_message(MessageId, #{status => cancelled}) of
        ok ->
            {reply, {ok, cancelled}, State};
        {error, _} = Error ->
            {reply, Error, State}
    end;

handle_call({get_config, Section}, _From, #state{config = undefined} = State) ->
    io:format("Server: Config not in state, loading from DB: ~p~n", [Section]),
    case smsc_db:get_config(Section) of
        {ok, Config} ->
            io:format("Server: Retrieved config from DB: ~p~n", [Config]),
            {reply, {ok, maps:merge(Config, #{<<"section">> => Section})}, State#state{config = Config}};
        {error, not_found} ->
            % Use default config
            DefaultConfig = #{
                <<"smsc_host">> => <<"localhost">>,
                <<"smsc_port">> => 2775,
                <<"system_id">> => <<"test_system">>,
                <<"password">> => <<"test_password">>,
                <<"max_retries">> => 3,
                <<"retry_delay">> => 60,
                <<"system_type">> => <<"">>,
                <<"interface_version">> => 52,
                <<"reconnect_interval">> => 5,
                <<"enquire_link_interval">> => 30,
                <<"section">> => Section
            },
            io:format("Server: Using default config: ~p~n", [DefaultConfig]),
            % Save default config to database
            case smsc_db:save_config(Section, DefaultConfig) of
                ok ->
                    io:format("Server: Saved default config to DB~n"),
                    {reply, {ok, DefaultConfig}, State#state{config = DefaultConfig}};
                Error ->
                    io:format("Server: Error saving default config: ~p~n", [Error]),
                    {reply, Error, State}
            end;
        Error ->
            io:format("Server: Error getting config: ~p~n", [Error]),
            {reply, Error, State}
    end;

handle_call({get_config, Section}, _From, #state{config = Config} = State) when Config =/= undefined ->
    io:format("Server: Returning config from state: ~p~n", [Config]),
    {reply, {ok, maps:merge(Config, #{<<"section">> => Section})}, State};

handle_call({update_config, Section, NewConfig}, _From, State) ->
    io:format("Server: Updating config for section ~p with: ~p~n", [Section, NewConfig]),
    case smsc_db:save_config(Section, NewConfig) of
        ok -> 
            io:format("Server: Config updated successfully~n"),
            {reply, {ok, NewConfig}, State#state{config = NewConfig}};
        Error -> 
            io:format("Server: Failed to update config: ~p~n", [Error]),
            {reply, Error, State}
    end;

handle_call(get_metrics, _From, State = #state{metrics = Metrics}) ->
    {reply, {ok, Metrics}, State};

handle_call(_Request, _From, State) ->
    {reply, {error, unknown_call}, State}.

handle_cast(_Msg, State) ->
    {noreply, State}.

handle_info(update_metrics, State) ->
    CurrentTime = erlang:system_time(second),
    _ = CurrentTime - State#state.last_metrics_update,
    
    % Get recent messages from database
    {ok, RecentMessages} = smsc_db:get_messages(10),
    
    % Calculate messages per second
    {ok, Stats} = calculate_message_stats(),
    
    % Update metrics
    NewMetrics = maps:merge(State#state.metrics, #{
        messages_per_second => maps:get(messages_per_second, Stats, 0),
        total_messages => maps:get(total_messages, Stats, 0),
        failed_messages => maps:get(failed_messages, Stats, 0),
        recent_messages => RecentMessages
    }),
    
    % Schedule next update
    erlang:send_after(1000, self(), update_metrics),
    
    {noreply, State#state{
        metrics = NewMetrics,
        last_metrics_update = CurrentTime
    }};

handle_info(_Info, State) ->
    {noreply, State}.

terminate(_Reason, _State) ->
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%%%===================================================================
%%% Internal functions
%%%===================================================================

generate_message_id() ->
    Now = erlang:system_time(microsecond),
    Random = rand:uniform(1000000),
    list_to_binary(integer_to_list(Now) ++ "-" ++ integer_to_list(Random)).

update_metrics_for_new_message(Metrics, _Message) ->
    {ok, RecentMessages} = smsc_db:get_messages(10),
    maps:merge(Metrics, #{recent_messages => RecentMessages}).

calculate_message_stats() ->
    % Calculate message statistics from database
    {ok, Conn} = smsc_db:connect(),
    Result = epgsql:squery(Conn,
        "SELECT "
        "COUNT(*) as total,"
        "SUM(CASE WHEN status = 'failed' THEN 1 ELSE 0 END) as failed,"
        "COUNT(*) FILTER (WHERE created_at > NOW() - INTERVAL '1 minute') as last_minute "
        "FROM smsc_messages"),
    smsc_db:disconnect(Conn),
    
    case Result of
        {ok, _, [{Total, Failed, LastMinute}]} ->
            {ok, #{
                total_messages => binary_to_integer(Total),
                failed_messages => binary_to_integer(Failed),
                messages_per_second => binary_to_integer(LastMinute) div 60
            }};
        Error ->
            Error
    end.
