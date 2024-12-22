%%%-------------------------------------------------------------------
%%% SMSC Core Implementation - Part 1 (Fixed)
%%% Core Definitions, Records, and Types
%%%-------------------------------------------------------------------

-module(smsc_core).

%% Split into separate behaviors to avoid conflicts
-behaviour(application).

%% Application exports
-export([start/2, stop/1]).

%% API exports
-export([submit_message/1, query_message/1, cancel_message/1,
         get_config/1, update_config/2,
         get_metrics/0, get_system_status/0]).

%% Include required libraries
-include_lib("kernel/include/logger.hrl").
-include_lib("stdlib/include/ms_transform.hrl").

%%%===================================================================
%%% Record Definitions (Reordered to resolve dependencies)
%%%===================================================================

%% First, define basic records with no dependencies
-record(connection_info, {
    type :: atom(),
    status :: atom(),
    connected_at :: integer(),
    last_active :: integer(),
    metadata :: map()
}).

-record(retry_config, {
    max_attempts :: pos_integer(),
    initial_delay :: pos_integer(),
    max_delay :: pos_integer(),
    backoff_factor :: float(),
    retry_on :: [atom()]
}).

-record(datetime_config, {
    timezone :: string(),
    validity_period :: pos_integer(),
    expiry_handling :: delete | archive,
    timestamp_format :: string()
}).

-record(sigtran_config, {
    local_ip :: inet:ip_address(),
    local_port :: inet:port_number(),
    remote_ip :: inet:ip_address(),
    remote_port :: inet:port_number(),
    routing_context :: integer(),
    asp_id :: integer(),
    network_appearance :: integer(),
    protocol_variant :: itu | ansi,
    network_indicators :: map()
}).

-record(message, {
    id :: binary(),
    source :: binary(),
    destination :: binary(),
    text :: binary(),
    submit_time :: integer(),
    validity_period :: integer(),
    priority :: 1..5,
    status :: atom(),
    retry_count :: non_neg_integer(),
    next_retry :: integer() | undefined
}).

%% Finally, define records that depend on others
-record(state, {
    config :: map(),
    retry_config :: #retry_config{},
    datetime_config :: #datetime_config{},
    sigtran_config :: #sigtran_config{},
    connections = #{} :: #{pid() => #connection_info{}},
    postgres_pool :: pid(),
    redis_pool :: pid()
}).

%%%===================================================================
%%% Type Definitions
%%%===================================================================

-type message_id() :: binary().
-type message_params() :: #{
    source := binary(),
    destination := binary(),
    text := binary(),
    priority => 1..5,
    validity_period => pos_integer()
}.
-type config_section() :: retry | datetime | sigtran.
-type storage_backend() :: mnesia | postgres | redis.

%% Add type exports if needed
-export_type([message_id/0, message_params/0, config_section/0, storage_backend/0]).

%%%===================================================================
%%% Default Configuration Functions
%%%===================================================================

load_initial_config() ->
    #{
        retry => init_retry_config(),
        datetime => init_datetime_config(),
        sigtran => init_sigtran_config()
    }.

init_retry_config() ->
    #retry_config{
        max_attempts = 3,
        initial_delay = 1000,
        max_delay = 30000,
        backoff_factor = 2.0,
        retry_on = [temporary_error, network_error, timeout]
    }.

init_datetime_config() ->
    #datetime_config{
        timezone = "UTC",
        validity_period = 86400,
        expiry_handling = delete,
        timestamp_format = "{{YYYY}}-{{MM}}-{{DD}}T{{hh}}:{{mm}}:{{ss}}Z"
    }.

init_sigtran_config() ->
    #sigtran_config{
        local_ip = {127,0,0,1},
        local_port = 2905,
        remote_ip = {127,0,0,1},
        remote_port = 2905,
        routing_context = 1,
        asp_id = 1,
        network_appearance = 1,
        protocol_variant = itu,
        network_indicators = #{}
    }.
	
%%%-------------------------------------------------------------------
%%% SMSC Core Implementation - Part 2 (Fixed)
%%% Application and Supervisor Implementation
%%%-------------------------------------------------------------------

%%%===================================================================
%%% Application callbacks
%%%===================================================================

start(_StartType, _StartArgs) ->
    % Initialize logger
    logger:set_primary_config(level, info),
    
    % Start supervisor
    smsc_sup:start_link().

stop(_State) ->
    ok.

%%%===================================================================
%%% Create a separate supervisor module
%%%===================================================================

-module(smsc_sup).
-behaviour(supervisor).

%% API
-export([start_link/0]).

%% Supervisor callbacks
-export([init/1]).

start_link() ->
    supervisor:start_link({local, ?MODULE}, ?MODULE, []).

init([]) ->
    % Initialize storage systems
    init_storage_systems(),
    
    % Initialize HTTP API
    init_http_api(),
    
    % Child specifications
    Children = [
        #{id => smsc_server,
          start => {smsc_server, start_link, []},
          restart => permanent,
          shutdown => 5000,
          type => worker,
          modules => [smsc_server]},
        
        #{id => smsc_monitoring,
          start => {smsc_monitoring, start_link, []},
          restart => permanent,
          shutdown => 5000,
          type => worker,
          modules => [smsc_monitoring]}
    ],
    
    % Supervisor specifications
    {ok, {#{strategy => one_for_one,
            intensity => 10,
            period => 60}, Children}}.

%%%===================================================================
%%% Storage initialization
%%%===================================================================

init_storage_systems() ->
    % Initialize Mnesia
    init_mnesia(),
    % Initialize PostgreSQL connection pool
    init_postgres(),
    % Initialize Redis connection pool
    init_redis().

init_mnesia() ->
    % Create Mnesia schema if it doesn't exist
    case mnesia:create_schema([node()]) of
        ok -> ok;
        {error, {_, {already_exists, _}}} -> ok;
        Error -> throw({mnesia_schema_creation_failed, Error})
    end,
    
    % Start Mnesia if not already started
    case mnesia:system_info(is_running) of
        no -> 
            case mnesia:start() of
                ok -> ok;
                Error -> throw({mnesia_start_failed, Error})
            end;
        _ -> ok
    end,
    
    % Create tables with proper error handling
    create_mnesia_tables().

create_mnesia_tables() ->
    TableSpecs = [
        {messages, [
            {attributes, record_info(fields, message)},
            {disc_copies, [node()]},
            {type, set}
        ]},
        {active_sessions, [
            {attributes, record_info(fields, connection_info)},
            {ram_copies, [node()]},
            {type, set}
        ]}
    ],
    create_tables(TableSpecs).

create_tables([]) -> ok;
create_tables([{Table, Opts} | Rest]) ->
    case mnesia:create_table(Table, Opts) of
        {atomic, ok} -> 
            create_tables(Rest);
        {aborted, {already_exists, Table}} -> 
            create_tables(Rest);
        Error -> 
            throw({table_creation_failed, Table, Error})
    end.

init_postgres() ->
    % Start the PostgreSQL connection pool with enhanced error handling
    PoolConfig = get_postgres_config(),
    case pgo:start_pool(smsc_pool, PoolConfig) of
        {ok, Pool} -> 
            validate_postgres_connection(Pool);
        Error ->
            logger:error("Failed to start PostgreSQL pool: ~p", [Error]),
            throw({failed_to_start_postgres, Error})
    end.

get_postgres_config() ->
    #{
        host => application:get_env(smsc_core, postgres_host, "localhost"),
        database => application:get_env(smsc_core, postgres_database, "smsc_db"),
        user => application:get_env(smsc_core, postgres_user, "smsc_user"),
        password => application:get_env(smsc_core, postgres_password, "smsc_password"),
        pool_size => application:get_env(smsc_core, postgres_pool_size, 10),
        timeout => application:get_env(smsc_core, postgres_timeout, 5000)
    }.

validate_postgres_connection(Pool) ->
    case pgo:query(Pool, "SELECT 1", [], #{timeout => 5000}) of
        {ok, _} -> Pool;
        Error ->
            logger:error("Failed to validate PostgreSQL connection: ~p", [Error]),
            throw({failed_to_connect_postgres, Error})
    end.

init_redis() ->
    % Start the Redis connection pool with enhanced error handling
    RedisConfig = get_redis_config(),
    case eredis_pool:start_pool(RedisConfig) of
        {ok, Pool} -> 
            validate_redis_connection(Pool);
        Error ->
            logger:error("Failed to start Redis pool: ~p", [Error]),
            throw({failed_to_start_redis, Error})
    end.

get_redis_config() ->
    #{
        host => application:get_env(smsc_core, redis_host, "localhost"),
        port => application:get_env(smsc_core, redis_port, 6379),
        database => application:get_env(smsc_core, redis_database, 0),
        password => application:get_env(smsc_core, redis_password, ""),
        pool_size => application:get_env(smsc_core, redis_pool_size, 5),
        timeout => application:get_env(smsc_core, redis_timeout, 5000)
    }.

validate_redis_connection(Pool) ->
    case eredis:q(Pool, ["PING"]) of
        {ok, <<"PONG">>} -> Pool;
        Error ->
            logger:error("Failed to validate Redis connection: ~p", [Error]),
            throw({failed_to_connect_redis, Error})
    end.

%%%===================================================================
%%% HTTP API initialization
%%%===================================================================

init_http_api() ->
    Dispatch = cowboy_router:compile([
        {'_', [
            {"/api/messages", smsc_http_handler, []},
            {"/api/messages/:id", smsc_http_handler, []},
            {"/api/config/:section", smsc_http_handler, []},
            {"/api/monitoring/metrics", smsc_http_handler, []},
            {"/api/monitoring/status", smsc_http_handler, []}
        ]}
    ]),
    
    Port = application:get_env(smsc_core, http_port, 8080),
    TransportOpts = [{port, Port}],
    ProtocolOpts = #{
        env => #{dispatch => Dispatch},
        stream_handlers => [cowboy_stream_h],
        max_connections => application:get_env(smsc_core, max_http_connections, 1000)
    },
    
    case cowboy:start_clear(http_listener, TransportOpts, ProtocolOpts) of
        {ok, _} -> ok;
        Error -> throw({failed_to_start_http, Error})
    end.
	
%%%-------------------------------------------------------------------
%%% SMSC Core Implementation - Part 3 (Fixed)
%%% Server Implementation
%%%-------------------------------------------------------------------

-module(smsc_server).
-behaviour(gen_server).

%% API
-export([start_link/0]).

%% gen_server callbacks
-export([init/1, handle_call/3, handle_cast/2, handle_info/2,
         terminate/2, code_change/3]).

%%%===================================================================
%%% API Functions
%%%===================================================================

start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

%%%===================================================================
%%% Gen Server Implementation
%%%===================================================================

init([]) ->
    process_flag(trap_exit, true),
    try
        State = #state{
            config = smsc_core:load_initial_config(),
            retry_config = smsc_core:init_retry_config(),
            datetime_config = smsc_core:init_datetime_config(),
            sigtran_config = smsc_core:init_sigtran_config(),
            connections = #{},
            postgres_pool = whereis(smsc_pool),
            redis_pool = whereis(eredis_pool)
        },
        {ok, State}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Server initialization failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {stop, {initialization_failed, Error}}
    end.

%%%===================================================================
%%% Call Handlers
%%%===================================================================

handle_call({submit_message, Params}, From, State) ->
    try
        spawn_monitor(fun() ->
            Result = process_message_submission(Params, State),
            gen_server:reply(From, Result)
        end),
        {noreply, State}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message submission failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {reply, {error, submission_failed}, State}
    end;

handle_call({query_message, MessageId}, _From, State) ->
    try
        Result = lookup_message(MessageId),
        {reply, Result, State}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message query failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {reply, {error, query_failed}, State}
    end;

handle_call({cancel_message, MessageId}, _From, State) ->
    try
        Result = cancel_message_impl(MessageId),
        {reply, Result, State}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message cancellation failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {reply, {error, cancellation_failed}, State}
    end;

handle_call({get_config, Section}, _From, State) ->
    try
        Config = get_section_config(Section, State),
        {reply, {ok, Config}, State}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Config retrieval failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {reply, {error, config_retrieval_failed}, State}
    end;

handle_call({update_config, Section, NewConfig}, _From, State) ->
    try
        case validate_and_update_config(Section, NewConfig, State) of
            {ok, UpdatedState} -> 
                {reply, ok, UpdatedState};
            {error, Reason} -> 
                {reply, {error, Reason}, State}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Config update failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {reply, {error, config_update_failed}, State}
    end;

handle_call(get_metrics, _From, State) ->
    try
        Metrics = collect_metrics(State),
        {reply, {ok, Metrics}, State}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Metrics collection failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {reply, {error, metrics_collection_failed}, State}
    end;

handle_call(get_system_status, _From, State) ->
    try
        Status = get_system_info(State),
        {reply, {ok, Status}, State}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Status retrieval failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {reply, {error, status_retrieval_failed}, State}
    end;

handle_call(_Request, _From, State) ->
    {reply, {error, unknown_request}, State}.

%%%===================================================================
%%% Cast Handlers
%%%===================================================================

handle_cast({retry_message, MessageId}, State) ->
    try
        case handle_message_retry(MessageId, State) of
            {ok, NewState} -> {noreply, NewState};
            {error, _} -> {noreply, State}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message retry failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {noreply, State}
    end;

handle_cast(_Msg, State) ->
    {noreply, State}.

%%%===================================================================
%%% Info Handlers
%%%===================================================================

handle_info({retry_timeout, MessageId}, State) ->
    try
        handle_retry_timeout(MessageId, State),
        {noreply, State}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Retry timeout handling failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {noreply, State}
    end;

handle_info({'EXIT', Pid, Reason}, State) ->
    try
        NewState = handle_connection_exit(Pid, Reason, State),
        {noreply, NewState}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Connection exit handling failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {noreply, State}
    end;

handle_info({'DOWN', _Ref, process, _Pid, normal}, State) ->
    % Normal process termination, ignore
    {noreply, State};

handle_info({'DOWN', _Ref, process, Pid, Reason}, State) ->
    logger:warning("Monitored process ~p terminated: ~p", [Pid, Reason]),
    {noreply, State};

handle_info(_Info, State) ->
    {noreply, State}.

%%%===================================================================
%%% Termination
%%%===================================================================

terminate(Reason, State) ->
    try
        logger:info("SMSC Server terminating: ~p", [Reason]),
        cleanup_resources(State)
    catch
        Kind:Error:Stacktrace ->
            logger:error("Termination cleanup failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace])
    end,
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%%%===================================================================
%%% Internal Functions
%%%===================================================================

process_message_submission(Params, State) ->
    Message = create_message(Params, State),
    case validate_message(Message, State) of
        ok ->
            handle_message_submission(Message, State);
        {error, _} = Error ->
            Error
    end.

get_section_config(Section, State) ->
    case Section of
        retry -> State#state.retry_config;
        datetime -> State#state.datetime_config;
        sigtran -> State#state.sigtran_config;
        _ -> {error, invalid_section}
    end.

validate_and_update_config(Section, NewConfig, State) ->
    try
        case validate_section_config(Section, NewConfig) of
            ok ->
                UpdatedState = update_state_config(Section, NewConfig, State),
                store_config_postgres(Section, NewConfig),
                {ok, UpdatedState};
            Error ->
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Config validation failed: ~p:~p~n~p", 
                        [Kind, Error, Stacktrace]),
            {error, validation_failed}
    end.

cleanup_resources(State) ->
    % Close all active connections
    maps:foreach(
        fun(Pid, _) -> 
            close_connection(Pid)
        end,
        State#state.connections
    ),
    % Ensure proper database shutdown
    close_database_connections(State).
	
%%%-------------------------------------------------------------------
%%% SMSC Core Implementation - Part 4 (Fixed)
%%% Message Processing and Storage Operations
%%%-------------------------------------------------------------------

%%%===================================================================
%%% Message Processing Functions
%%%===================================================================

create_message(Params, State) ->
    Now = erlang:system_time(millisecond),
    ValidityPeriod = maps:get(validity_period, Params,
                             State#state.datetime_config#datetime_config.validity_period),
    
    #message{
        id = generate_message_id(),
        source = maps:get(source, Params),
        destination = maps:get(destination, Params),
        text = maps:get(text, Params),
        submit_time = Now,
        validity_period = Now + ValidityPeriod * 1000,
        priority = maps:get(priority, Params, 3),
        status = pending,
        retry_count = 0,
        next_retry = undefined
    }.

handle_message_submission(Message, State) ->
    try
        % Store in PostgreSQL first for persistence
        case store_message_postgres(Message) of
            ok ->
                % Then store in Mnesia for active processing
                case store_message_mnesia(Message) of
                    ok ->
                        % Update Redis counters
                        ok = increment_message_counter(),
                        % Try to send the message
                        case send_message(Message, State) of
                            ok ->
                                {ok, Message#message.id};
                            {error, Reason} ->
                                handle_send_error(Message, Reason, State)
                        end;
                    Error -> Error
                end;
            Error -> Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message submission failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, submission_failed}
    end.

handle_send_error(Message, Reason, State) ->
    try
        case should_retry(Message, Reason, State) of
            true ->
                schedule_retry(Message, State),
                {ok, Message#message.id};
            false ->
                mark_message_failed(Message, Reason),
                {error, sending_failed}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Error handling failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, error_handling_failed}
    end.

handle_message_retry(MessageId, State) ->
    try
        case get_message(MessageId) of
            {ok, Message} ->
                case should_retry(Message, retry_attempt, State) of
                    true ->
                        case send_message(Message, State) of
                            ok ->
                                update_message_status(Message#message{
                                    status = delivered,
                                    next_retry = undefined
                                }),
                                {ok, State};
                            {error, Reason} ->
                                handle_retry_error(Message, Reason, State)
                        end;
                    false ->
                        mark_message_failed(Message, max_retries_exceeded),
                        {error, max_retries_exceeded}
                end;
            Error ->
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message retry failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, retry_failed}
    end.

%%%===================================================================
%%% Storage Operations
%%%===================================================================

store_message_postgres(Message) ->
    Query = "INSERT INTO messages (id, source, destination, text, submit_time, 
             validity_period, priority, status, retry_count, next_retry) 
             VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)",
    Params = [
        Message#message.id,
        Message#message.source,
        Message#message.destination,
        Message#message.text,
        Message#message.submit_time,
        Message#message.validity_period,
        Message#message.priority,
        atom_to_binary(Message#message.status, utf8),
        Message#message.retry_count,
        Message#message.next_retry
    ],
    try
        case pgo:query(Query, Params) of
            {ok, _} -> ok;
            {error, Reason} -> 
                logger:error("PostgreSQL storage error: ~p", [Reason]),
                {error, {postgres_error, Reason}}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("PostgreSQL exception: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, postgres_exception}
    end.

store_message_mnesia(Message) ->
    try
        F = fun() ->
            mnesia:write(messages, Message, write)
        end,
        case mnesia:transaction(F) of
            {atomic, ok} -> ok;
            {aborted, Reason} ->
                logger:error("Mnesia storage error: ~p", [Reason]),
                {error, {mnesia_error, Reason}}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Mnesia exception: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, mnesia_exception}
    end.

update_message_mnesia(Message) ->
    try
        F = fun() ->
            mnesia:write(messages, Message, write)
        end,
        case mnesia:transaction(F) of
            {atomic, ok} -> ok;
            {aborted, Reason} ->
                logger:error("Mnesia update error: ~p", [Reason]),
                {error, {mnesia_error, Reason}}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Mnesia update exception: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, mnesia_update_exception}
    end.

update_message_postgres(Message) ->
    Query = "UPDATE messages SET status = $1, retry_count = $2, next_retry = $3 
             WHERE id = $4",
    Params = [
        atom_to_binary(Message#message.status, utf8),
        Message#message.retry_count,
        Message#message.next_retry,
        Message#message.id
    ],
    try
        case pgo:query(Query, Params) of
            {ok, _} -> ok;
            {error, Reason} ->
                logger:error("PostgreSQL update error: ~p", [Reason]),
                {error, {postgres_error, Reason}}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("PostgreSQL update exception: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, postgres_update_exception}
    end.

get_message(MessageId) ->
    % Try Mnesia first for active messages
    case get_message_mnesia(MessageId) of
        {ok, Message} -> 
            {ok, Message};
        {error, not_found} ->
            % Fall back to PostgreSQL for historical messages
            get_message_postgres(MessageId);
        Error ->
            Error
    end.

get_message_mnesia(MessageId) ->
    try
        case mnesia:dirty_read(messages, MessageId) of
            [Message] -> {ok, Message};
            [] -> {error, not_found}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Mnesia read error: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, mnesia_read_error}
    end.

get_message_postgres(MessageId) ->
    Query = "SELECT * FROM messages WHERE id = $1",
    try
        case pgo:query(Query, [MessageId]) of
            {ok, #{rows := [Row]}} -> {ok, row_to_message(Row)};
            {ok, #{rows := []}} -> {error, not_found};
            {error, Reason} ->
                logger:error("PostgreSQL read error: ~p", [Reason]),
                {error, {postgres_read_error, Reason}}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("PostgreSQL read exception: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, postgres_read_exception}
    end.

row_to_message(Row) ->
    try
        #message{
            id = maps:get(<<"id">>, Row),
            source = maps:get(<<"source">>, Row),
            destination = maps:get(<<"destination">>, Row),
            text = maps:get(<<"text">>, Row),
            submit_time = maps:get(<<"submit_time">>, Row),
            validity_period = maps:get(<<"validity_period">>, Row),
            priority = maps:get(<<"priority">>, Row),
            status = binary_to_atom(maps:get(<<"status">>, Row)),
            retry_count = maps:get(<<"retry_count">>, Row),
            next_retry = maps:get(<<"next_retry">>, Row)
        }
    catch
        Kind:Error:Stacktrace ->
            logger:error("Row conversion error: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            throw({row_conversion_error, Row})
    end.
	
%%%-------------------------------------------------------------------
%%% SMSC Core Implementation - Part 5 (Fixed)
%%% Message Sending and Connection Management
%%%-------------------------------------------------------------------

%%%===================================================================
%%% Message Sending Implementation
%%%===================================================================

send_message(Message, State) ->
    try
        % Select sending strategy based on priority
        case Message#message.priority of
            1 -> % High priority
                send_high_priority_message(Message, State);
            2 -> % Medium priority
                send_medium_priority_message(Message, State);
            _ -> % Normal priority
                send_normal_priority_message(Message, State)
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message sending failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, sending_failed}
    end.

send_high_priority_message(Message, State) ->
    SendOpts = #{
        timeout => 5000,
        retries => 3,
        connection_pool => high_priority,
        queue_strategy => immediate,
        max_queue_length => 100
    },
    send_message_with_options(Message, State, SendOpts).

send_medium_priority_message(Message, State) ->
    SendOpts = #{
        timeout => 10000,
        retries => 2,
        connection_pool => medium_priority,
        queue_strategy => standard,
        max_queue_length => 500
    },
    send_message_with_options(Message, State, SendOpts).

send_normal_priority_message(Message, State) ->
    SendOpts = #{
        timeout => 30000,
        retries => 1,
        connection_pool => normal_priority,
        queue_strategy => batch,
        max_queue_length => 1000
    },
    send_message_with_options(Message, State, SendOpts).

send_message_with_options(Message, State, Options) ->
    try
        ConnectionPool = maps:get(connection_pool, Options),
        Timeout = maps:get(timeout, Options),
        
        case acquire_connection(ConnectionPool, State) of
            {ok, Connection} ->
                try
                    handle_message_transmission(Message, Connection, Timeout)
                after
                    release_connection(Connection)
                end;
            {error, Reason} ->
                logger:error("Connection acquisition failed: ~p", [Reason]),
                {error, connection_failed}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message transmission failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, transmission_failed}
    end.

%%%===================================================================
%%% Connection Management
%%%===================================================================

acquire_connection(Pool, State) ->
    try
        case get_available_connection(Pool, State) of
            {ok, Connection} ->
                {ok, Connection};
            {error, no_connection} ->
                create_new_connection(Pool, State);
            Error ->
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Connection acquisition failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, connection_failed}
    end.

get_available_connection(Pool, State) ->
    case maps:get(Pool, State#state.connections, []) of
        [] ->
            {error, no_connection};
        Connections when is_list(Connections) ->
            select_least_loaded_connection(Connections);
        _ ->
            {error, invalid_pool}
    end.

select_least_loaded_connection(Connections) ->
    try
        case lists:sort(
            fun(C1, C2) -> 
                connection_load(C1) =< connection_load(C2)
            end, 
            Connections) of
            [BestConn|_] -> {ok, BestConn};
            [] -> {error, no_connection}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Connection selection failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, selection_failed}
    end.

connection_load(Connection) ->
    try
        case erlang:process_info(Connection, message_queue_len) of
            {message_queue_len, Length} -> Length;
            undefined -> infinity
        end
    catch
        _:_ -> infinity
    end.

create_new_connection(Pool, State) ->
    try
        ConnectionOpts = get_connection_opts(Pool, State),
        case establish_connection(ConnectionOpts) of
            {ok, Connection} = Result ->
                monitor_connection(Connection, Pool),
                Result;
            Error ->
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Connection creation failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, creation_failed}
    end.

get_connection_opts(Pool, State) ->
    BaseOpts = #{
        host => application:get_env(smsc_core, smsc_host, "localhost"),
        port => application:get_env(smsc_core, smsc_port, 2775),
        system_id => application:get_env(smsc_core, system_id, "test_system"),
        password => application:get_env(smsc_core, password, "test_pass")
    },
    add_pool_specific_opts(BaseOpts, Pool, State).

add_pool_specific_opts(BaseOpts, high_priority, _State) ->
    BaseOpts#{
        bind_type => transceiver,
        window_size => 100,
        response_timeout => 5000
    };
add_pool_specific_opts(BaseOpts, medium_priority, _State) ->
    BaseOpts#{
        bind_type => transceiver,
        window_size => 50,
        response_timeout => 10000
    };
add_pool_specific_opts(BaseOpts, normal_priority, _State) ->
    BaseOpts#{
        bind_type => transceiver,
        window_size => 25,
        response_timeout => 30000
    }.

establish_connection(Opts) ->
    try
        % Implement actual SMPP connection establishment here
        % For now, simulate connection creation
        {ok, spawn_link(fun() -> connection_process(Opts) end)}
    catch
        Kind:Error:Stacktrace ->
            logger:error("Connection establishment failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, establishment_failed}
    end.

connection_process(Opts) ->
    process_flag(trap_exit, true),
    connection_loop(Opts, #{}).

connection_loop(Opts, State) ->
    receive
        {send, Message, From} ->
            Result = handle_send(Message, Opts, State),
            From ! {send_result, Result},
            connection_loop(Opts, State);
        {update_state, NewState} ->
            connection_loop(Opts, NewState);
        {'EXIT', _, Reason} ->
            logger:info("Connection terminating: ~p", [Reason]),
            ok;
        Other ->
            logger:warning("Unknown connection message: ~p", [Other]),
            connection_loop(Opts, State)
    end.

handle_send(Message, Opts, State) ->
    try
        % Simulate message sending with success probability
        case rand:uniform(100) of
            N when N =< 95 -> ok;
            _ -> {error, network_error}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Send handling failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, send_failed}
    end.

release_connection(Connection) ->
    Connection ! {update_state, #{status => available}}.

monitor_connection(Connection, Pool) ->
    ConnectionInfo = #connection_info{
        type = Pool,
        status = active,
        connected_at = erlang:system_time(second),
        last_active = erlang:system_time(second),
        metadata = #{
            pool => Pool,
            pid => Connection
        }
    },
    erlang:monitor(process, Connection),
    ets:insert(connection_registry, {Connection, ConnectionInfo}).
	
%%%-------------------------------------------------------------------
%%% SMSC Core Implementation - Part 6 (Fixed)
%%% Error Handling, Configuration Management, and Utility Functions
%%%-------------------------------------------------------------------

%%%===================================================================
%%% Error Handling Functions
%%%===================================================================

handle_retry_error(Message, Reason, State) ->
    try
        case should_retry(Message, Reason, State) of
            true ->
                NewState = schedule_retry(Message, State),
                {ok, NewState};
            false ->
                mark_message_failed(Message, Reason),
                {error, max_retries_exceeded}
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Retry error handling failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, retry_handling_failed}
    end.

should_retry(Message, Reason, State) ->
    try
        RetryConfig = State#state.retry_config,
        RetryableReason = lists:member(Reason, RetryConfig#retry_config.retry_on),
        UnderMaxAttempts = Message#message.retry_count < RetryConfig#retry_config.max_attempts,
        NotExpired = not is_message_expired(Message),
        RetryableReason andalso UnderMaxAttempts andalso NotExpired
    catch
        Kind:Error:Stacktrace ->
            logger:error("Retry check failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            false
    end.

mark_message_failed(Message, Reason) ->
    try
        FailedMessage = Message#message{
            status = failed,
            next_retry = undefined
        },
        case update_message_status(FailedMessage) of
            ok -> 
                log_message_failure(FailedMessage, Reason),
                ok;
            Error -> 
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Failed to mark message as failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, status_update_failed}
    end.

%%%===================================================================
%%% Configuration Management
%%%===================================================================

validate_section_config(Section, NewConfig) ->
    try
        Validator = get_section_validator(Section),
        case Validator(NewConfig) of
            ok -> ok;
            {error, Reason} = Error ->
                logger:error("Config validation failed for ~p: ~p", [Section, Reason]),
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Config validation error: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, validation_error}
    end.

get_section_validator(retry) ->
    fun validate_retry_config/1;
get_section_validator(datetime) ->
    fun validate_datetime_config/1;
get_section_validator(sigtran) ->
    fun validate_sigtran_config/1;
get_section_validator(_) ->
    fun(_) -> {error, invalid_section} end.

validate_retry_config(Config) ->
    try
        Required = [max_attempts, initial_delay, max_delay, backoff_factor, retry_on],
        case validate_required_fields(Config, Required) of
            ok ->
                validate_retry_values(Config);
            Error ->
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Retry config validation failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, validation_failed}
    end.

validate_datetime_config(Config) ->
    try
        Required = [timezone, validity_period, expiry_handling, timestamp_format],
        case validate_required_fields(Config, Required) of
            ok ->
                validate_datetime_values(Config);
            Error ->
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Datetime config validation failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, validation_failed}
    end.

validate_sigtran_config(Config) ->
    try
        Required = [local_ip, local_port, remote_ip, remote_port,
                   routing_context, asp_id, network_appearance],
        case validate_required_fields(Config, Required) of
            ok ->
                validate_sigtran_values(Config);
            Error ->
                Error
        end
    catch
        Kind:Error:Stacktrace ->
            logger:error("Sigtran config validation failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            {error, validation_failed}
    end.

%%%===================================================================
%%% Utility Functions
%%%===================================================================

generate_message_id() ->
    try
        Timestamp = erlang:system_time(microsecond),
        Random = crypto:strong_rand_bytes(8),
        Base64 = base64:encode(<<Timestamp:64, Random/binary>>),
        binary:replace(Base64, [<<"+">>, <<"/">>, <<"=">>], <<"-">>, [global])
    catch
        Kind:Error:Stacktrace ->
            logger:error("Message ID generation failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            throw(message_id_generation_failed)
    end.

format_timestamp(Timestamp) ->
    try
        {{Year, Month, Day}, {Hour, Minute, Second}} =
            calendar:system_time_to_universal_time(Timestamp, millisecond),
        lists:flatten(
            io_lib:format(
                "~4..0B-~2..0B-~2..0BT~2..0B:~2..0B:~2..0BZ",
                [Year, Month, Day, Hour, Minute, Second]
            )
        )
    catch
        Kind:Error:Stacktrace ->
            logger:error("Timestamp formatting failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            "invalid_timestamp"
    end.

get_system_info(State) ->
    try
        #{
            version => get_version_info(),
            uptime => get_system_uptime(),
            memory => erlang:memory(),
            process_count => erlang:system_info(process_count),
            connection_stats => get_connection_stats(State),
            message_stats => get_message_stats(),
            database_stats => get_database_stats()
        }
    catch
        Kind:Error:Stacktrace ->
            logger:error("System info collection failed: ~p:~p~n~p",
                        [Kind, Error, Stacktrace]),
            #{error => system_info_failed}
    end.

get_version_info() ->
    #{
        version => "1.0.0",
        build_date => "2024-03-20",
        erlang_version => erlang:system_info(version),
        system_architecture => erlang:system_info(system_architecture)
    }.

get_system_uptime() ->
    try
        {UpTime, _} = erlang:statistics(wall_clock),
        Seconds = UpTime div 1000,
        format_uptime(Seconds)
    catch
        _:_ -> "unknown"
    end.

format_uptime(Seconds) when Seconds < 60 ->
    integer_to_list(Seconds) ++ "s";
format_uptime(Seconds) when Seconds < 3600 ->
    Minutes = Seconds div 60,
    integer_to_list(Minutes) ++ "m";
format_uptime(Seconds) when Seconds < 86400 ->
    Hours = Seconds div 3600,
    integer_to_list(Hours) ++ "h";
format_uptime(Seconds) ->
    Days = Seconds div 86400,
    integer_to_list(Days) ++ "d".

%%%===================================================================
%%% Helper Functions
%%%===================================================================

validate_required_fields(Config, Required) ->
    Missing = [Field || Field <- Required, not maps:is_key(Field, Config)],
    case Missing of
        [] -> ok;
        Fields -> {error, {missing_fields, Fields}}
    end.

validate_retry_values(Config) ->
    try
        MaxAttempts = maps:get(max_attempts, Config),
        InitialDelay = maps:get(initial_delay, Config),
        MaxDelay = maps:get(max_delay, Config),
        BackoffFactor = maps:get(backoff_factor, Config),
        
        ValidMaxAttempts = is_integer(MaxAttempts) andalso MaxAttempts > 0,
        ValidInitialDelay = is_integer(InitialDelay) andalso InitialDelay > 0,
        ValidMaxDelay = is_integer(MaxDelay) andalso MaxDelay >= InitialDelay,
        ValidBackoffFactor = is_float(BackoffFactor) andalso BackoffFactor >= 1.0,
        
        case {ValidMaxAttempts, ValidInitialDelay, ValidMaxDelay, ValidBackoffFactor} of
            {true, true, true, true} -> ok;
            {false, _, _, _} -> {error, invalid_max_attempts};
            {_, false, _, _} -> {error, invalid_initial_delay};
            {_, _, false, _} -> {error, invalid_max_delay};
            {_, _, _, false} -> {error, invalid_backoff_factor}
        end
    catch
        _:_ -> {error, invalid_retry_config}
    end.

validate_datetime_values(Config) ->
    try
        Timezone = maps:get(timezone, Config),
        ValidityPeriod = maps:get(validity_period, Config),
        ExpiryHandling = maps:get(expiry_handling, Config),
        
        ValidTimezone = is_list(Timezone) andalso length(Timezone) > 0,
        ValidValidityPeriod = is_integer(ValidityPeriod) andalso ValidityPeriod > 0,
        ValidExpiryHandling = lists:member(ExpiryHandling, [delete, archive]),
        
        case {ValidTimezone, ValidValidityPeriod, ValidExpiryHandling} of
            {true, true, true} -> ok;
            {false, _, _} -> {error, invalid_timezone};
            {_, false, _} -> {error, invalid_validity_period};
            {_, _, false} -> {error, invalid_expiry_handling}
        end
    catch
        _:_ -> {error, invalid_datetime_config}
    end.

validate_sigtran_values(Config) ->
    try
        validate_ip_address(maps:get(local_ip, Config)) andalso
        validate_port_number(maps:get(local_port, Config)) andalso
        validate_ip_address(maps:get(remote_ip, Config)) andalso
        validate_port_number(maps:get(remote_port, Config))
    of
        true -> ok;
        false -> {error, invalid_network_config}
    catch
        _:_ -> {error, invalid_sigtran_config}
    end.

validate_ip_address({A,B,C,D}) when 
    is_integer(A), is_integer(B), is_integer(C), is_integer(D),
    A >= 0, A =< 255, B >= 0, B =< 255,
    C >= 0, C =< 255, D >= 0, D =< 255 -> true;
validate_ip_address(_) -> false.

validate_port_number(Port) when is_integer(Port), Port > 0, Port < 65536 -> true;
validate_port_number(_) -> false.
