%%%-------------------------------------------------------------------
%%% @doc
%%% SMSC Database Interface
%%% @end
%%%-------------------------------------------------------------------
-module(smsc_db).

-export([init/0, connect/0, disconnect/1]).
-export([save_config/2, get_config/1, get_all_config/0]).
-export([save_message/1, update_message/2, get_message/1, get_messages/1]).

-include_lib("kernel/include/logger.hrl").

%% Database initialization
init() ->
    {ok, Conn} = connect(),
    try
        % Create the config table if it doesn't exist
        CreateTableSql = "CREATE TABLE IF NOT EXISTS smsc_config (
            key TEXT PRIMARY KEY,
            value JSONB NOT NULL
        )",
        case epgsql:squery(Conn, CreateTableSql) of
            {ok, [], []} -> 
                io:format("DB: Config table created or already exists~n"),
                % Insert default config if it doesn't exist
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
                    <<"enquire_link_interval">> => 30
                },
                JsonValue = jsx:encode(DefaultConfig),
                InsertSql = "INSERT INTO smsc_config (key, value) 
                           VALUES ($1, $2::jsonb) 
                           ON CONFLICT (key) DO NOTHING",
                case epgsql:equery(Conn, InsertSql, [<<"smsc_config">>, JsonValue]) of
                    {ok, _} -> 
                        io:format("DB: Default config inserted or already exists~n"),
                        ok;
                    Error -> 
                        io:format("DB: Error inserting default config: ~p~n", [Error]),
                        Error
                end;
            Error -> 
                io:format("DB: Error creating config table: ~p~n", [Error]),
                Error
        end
    after
        disconnect(Conn)
    end.

%% Database connection management
connect() ->
    Host = application:get_env(smsc_core, postgres_host, "localhost"),
    Port = application:get_env(smsc_core, postgres_port, 5432),
    Database = application:get_env(smsc_core, postgres_database, "smsc_db"),
    User = application:get_env(smsc_core, postgres_user, "smsc_user"),
    Password = application:get_env(smsc_core, postgres_password, "smsc_password"),
    
    io:format("DB: Connecting to PostgreSQL~n"
              "Host: ~p~n"
              "Port: ~p~n"
              "Database: ~p~n"
              "User: ~p~n", [Host, Port, Database, User]),
    
    ConnResult = epgsql:connect(#{
        host => Host,
        port => Port,
        database => Database,
        username => User,
        password => Password
    }),
    
    case ConnResult of
        {ok, Conn} ->
            io:format("DB: Successfully connected to PostgreSQL~n"),
            {ok, Conn};
        {error, Error} ->
            io:format("DB: Failed to connect to PostgreSQL: ~p~n", [Error]),
            {error, Error}
    end.

disconnect(Conn) ->
    epgsql:close(Conn).

%% Configuration management
save_config(Key, Value) when is_binary(Key) ->
    io:format("DB: Saving config~nKey: ~p~nValue: ~p~n", [Key, Value]),
    case connect() of
        {ok, Conn} ->
            try
                % Convert the map to a JSON string
                JsonValue = jsx:encode(Value),
                io:format("DB: Encoded JSON value: ~p~n", [JsonValue]),
                
                % First, try to delete any existing config
                DeleteSql = "DELETE FROM smsc_config WHERE key = $1",
                io:format("DB: Deleting existing config with key: ~p~n", [Key]),
                _ = epgsql:equery(Conn, DeleteSql, [Key]),
                
                % Then insert the new config
                Sql = "INSERT INTO smsc_config (key, value) VALUES ($1, $2::jsonb)",
                io:format("DB: Executing SQL: ~s~nParameters: [~p, ~p]~n", [Sql, Key, JsonValue]),
                
                case epgsql:equery(Conn, Sql, [Key, JsonValue]) of
                    {ok, _} -> 
                        io:format("DB: Config saved successfully~n"),
                        ok;
                    Error ->
                        io:format("DB: Error saving config: ~p~n", [Error]),
                        {error, Error}
                end
            catch
                Type:What ->
                    io:format("DB: Error saving config:~nType: ~p~nError: ~p~n", 
                             [Type, What]),
                    {error, {save_error, What}}
            after
                disconnect(Conn)
            end;
        {error, Error} ->
            io:format("DB: Failed to connect: ~p~n", [Error]),
            {error, Error}
    end.

get_config(Key) when is_binary(Key) ->
    io:format("~n~n=== DB: Getting config for key: ~p ===~n", [Key]),
    case connect() of
        {ok, Conn} ->
            try
                % Construct the SQL query with explicit column names and compact JSON
                Sql = "SELECT value FROM smsc_config WHERE key = $1",
                io:format("=== DB: Executing query: ~s with key: ~p ===~n", [Sql, Key]),
                case epgsql:equery(Conn, Sql, [Key]) of
                    {ok, _, [{Value}]} ->
                        io:format("=== DB: Raw value from DB: ~p ===~n", [Value]),
                        % Parse the JSONB value into an Erlang map
                        try
                            Config = jsx:decode(Value, [return_maps]),
                            io:format("=== DB: Successfully decoded config: ~p ===~n", [Config]),
                            {ok, Config}
                        catch
                            Error:Reason ->
                                io:format("=== DB: Error decoding JSON:~nError: ~p~nReason: ~p ===~n", 
                                         [Error, Reason]),
                                {error, {decode_error, Reason}}
                        end;
                    {ok, _, []} ->
                        io:format("=== DB: No config found for key: ~p ===~n", [Key]),
                        {error, not_found};
                    Error ->
                        io:format("=== DB: Database error: ~p ===~n", [Error]),
                        {error, Error}
                end
            catch
                Type:What ->
                    io:format("=== DB: Error getting config:~nType: ~p~nError: ~p ===~n", 
                             [Type, What]),
                    {error, {fetch_error, What}}
            after
                disconnect(Conn)
            end;
        {error, Error} ->
            io:format("=== DB: Failed to connect: ~p ===~n", [Error]),
            {error, Error}
    end.

get_all_config() ->
    {ok, Conn} = connect(),
    try
        % Construct the SQL query
        Sql = "SELECT key, value FROM smsc_config",
        io:format("DB: Getting all config~nSQL: ~s~n", [Sql]),
        
        % Execute the query
        Result = epgsql:squery(Conn, Sql),
        io:format("DB: Query result: ~p~n", [Result]),
        
        disconnect(Conn),
        case Result of
            {ok, _, []} ->
                io:format("DB: No config found in database~n"),
                {error, not_found};
            {ok, _, Rows} ->
                try
                    % Process each row
                    Config = lists:foldl(
                        fun({Key, Value}, Acc) ->
                            io:format("DB: Processing row~nKey: ~p~nValue: ~p~n", [Key, Value]),
                            DecodedValue = jsx:decode(jsx:encode(Value), [return_maps]),
                            maps:put(Key, DecodedValue, Acc)
                        end,
                        #{},
                        Rows
                    ),
                    io:format("DB: Successfully processed all config: ~p~n", [Config]),
                    {ok, Config}
                catch
                    Error:Reason ->
                        io:format("DB: Error processing config:~nError: ~p~nReason: ~p~n", 
                                 [Error, Reason]),
                        {error, {config_processing_error, Reason}}
                end;
            {error, Error} ->
                io:format("DB: Database error: ~p~n", [Error]),
                {error, Error};
            Other ->
                io:format("DB: Unexpected result: ~p~n", [Other]),
                {error, Other}
        end
    catch
        Type:What ->
            io:format("DB: Error in get_all_config:~nType: ~p~nError: ~p~n", 
                     [Type, What]),
            disconnect(Conn),
            {error, {get_all_error, What}}
    end.

%% Message management
save_message(#{id := Id, content := Content, priority := Priority, status := Status}) ->
    {ok, Conn} = connect(),
    Result = epgsql:equery(Conn,
        "INSERT INTO smsc_messages (id, content, priority, status) "
        "VALUES ($1, $2, $3, $4)",
        [Id, Content, Priority, Status]),
    disconnect(Conn),
    case Result of
        {ok, _} -> ok;
        Error -> Error
    end.

update_message(Id, Updates) when is_map(Updates) ->
    {ok, Conn} = connect(),
    SetClauses = maps:fold(
        fun(K, _V, Acc) ->
            Field = atom_to_list(K),
            Acc ++ case Acc of
                [] -> Field ++ " = $2";
                _ -> ", " ++ Field ++ " = $" ++ integer_to_list(length(Acc) + 2)
            end
        end,
        "",
        Updates
    ),
    Values = [Id | maps:values(Updates)],
    Query = "UPDATE smsc_messages SET " ++ SetClauses ++ 
            ", updated_at = CURRENT_TIMESTAMP WHERE id = $1",
    Result = epgsql:equery(Conn, Query, Values),
    disconnect(Conn),
    case Result of
        {ok, N} when N > 0 -> ok;
        {ok, 0} -> {error, not_found};
        Error -> Error
    end.

get_message(Id) ->
    {ok, Conn} = connect(),
    Result = epgsql:equery(Conn,
        "SELECT id, content, priority, status, retries, "
        "created_at, updated_at FROM smsc_messages WHERE id = $1",
        [Id]),
    disconnect(Conn),
    case Result of
        {ok, _, [{Id, Content, Priority, Status, Retries, CreatedAt, UpdatedAt}]} ->
            {ok, #{
                id => Id,
                content => Content,
                priority => Priority,
                status => Status,
                retries => Retries,
                created_at => CreatedAt,
                updated_at => UpdatedAt
            }};
        {ok, _, []} -> {error, not_found};
        Error -> Error
    end.

get_messages(Limit) when is_integer(Limit), Limit > 0 ->
    {ok, Conn} = connect(),
    Result = epgsql:equery(Conn,
        "SELECT id, content, priority, status, retries, "
        "created_at, updated_at FROM smsc_messages "
        "ORDER BY created_at DESC LIMIT $1",
        [Limit]),
    disconnect(Conn),
    case Result of
        {ok, _, Rows} ->
            {ok, [#{
                id => Id,
                content => Content,
                priority => Priority,
                status => Status,
                retries => Retries,
                created_at => CreatedAt,
                updated_at => UpdatedAt
            } || {Id, Content, Priority, Status, Retries, CreatedAt, UpdatedAt} <- Rows]};
        Error -> Error
    end.
