%%%-------------------------------------------------------------------
%%% @doc
%%% SMSC HTTP API Handler
%%% @end
%%%-------------------------------------------------------------------
-module(smsc_http_handler).

-export([init/2]).

init(Req0=#{method := <<"OPTIONS">>}, State) ->
    Req = add_cors_headers(cowboy_req:reply(200, #{}, <<>>, Req0)),
    {ok, Req, State};

init(Req0=#{method := Method, path := Path} = _Req, State) ->
    Req1 = add_cors_headers(Req0),
    handle_request(Method, Path, Req1, State).

add_cors_headers(Req) ->
    Headers = #{
        <<"access-control-allow-origin">> => <<"*">>,
        <<"access-control-allow-methods">> => <<"GET, POST, DELETE, OPTIONS">>,
        <<"access-control-allow-headers">> => <<"content-type">>,
        <<"access-control-max-age">> => <<"3600">>
    },
    cowboy_req:set_resp_headers(Headers, Req).

handle_request(<<"POST">>, <<"/api/messages">>, Req0, State) ->
    {ok, Body, Req1} = cowboy_req:read_body(Req0),
    try
        Params = jsx:decode(Body, [return_maps]),
        case smsc_core:submit_message(Params) of
            {ok, MessageId} ->
                json_response(200, #{status => success, message_id => MessageId}, Req1, State);
            {error, Reason} ->
                json_response(400, #{status => error, reason => Reason}, Req1, State)
        end
    catch
        ErrorType:ErrorReason ->
            io:format("Error decoding message JSON: ~p:~p~nBody: ~p~n", 
                     [ErrorType, ErrorReason, Body]),
            json_response(400, #{status => error, reason => invalid_json}, Req1, State)
    end;

handle_request(<<"GET">>, <<"/api/messages/", MessageId/binary>>, Req, State) ->
    case smsc_core:query_message(MessageId) of
        {ok, Message} ->
            json_response(200, #{status => success, message => Message}, Req, State);
        {error, Reason} ->
            json_response(404, #{status => error, reason => Reason}, Req, State)
    end;

handle_request(<<"DELETE">>, <<"/api/messages/", MessageId/binary>>, Req, State) ->
    case smsc_core:cancel_message(MessageId) of
        ok ->
            json_response(200, #{status => success}, Req, State);
        {error, Reason} ->
            json_response(400, #{status => error, reason => Reason}, Req, State)
    end;

handle_request(<<"GET">>, <<"/api/metrics">>, Req, State) ->
    case smsc_core:get_metrics() of
        {ok, Metrics} ->
            json_response(200, #{status => success, metrics => Metrics}, Req, State);
        {error, Reason} ->
            json_response(500, #{status => error, reason => Reason}, Req, State)
    end;

handle_request(<<"GET">>, <<"/api/config">>, Req, State) ->
    io:format("~n=== Handling GET /api/config ===~n"),
    case smsc_core:get_config(<<"smsc_config">>) of
        {ok, Config} ->
            io:format("HTTP: Retrieved config from core: ~p~n", [Config]),
            % Return the config directly without any wrapping
            json_response(200, maps:without([section], Config), Req, State);
        {error, not_found} ->
            io:format("HTTP: Config not found~n"),
            json_response(404, #{
                status => error,
                reason => config_not_found
            }, Req, State);
        {error, Reason} ->
            io:format("HTTP: Error getting config: ~p~n", [Reason]),
            json_response(500, #{
                status => error,
                reason => Reason
            }, Req, State)
    end;

handle_request(<<"POST">>, <<"/api/config">>, Req0, State) ->
    io:format("~n=== Handling POST /api/config ===~n"),
    {ok, Body, Req1} = cowboy_req:read_body(Req0),
    io:format("Received body (raw): ~p~n", [Body]),
    io:format("Received body (as string): ~s~n", [Body]),
    try
        io:format("Attempting to decode JSON...~n"),
        Config = jsx:decode(Body, [return_maps]),
        io:format("Successfully decoded JSON: ~p~n", [Config]),
        Result = smsc_core:update_config(<<"smsc_config">>, Config),
        io:format("Update result: ~p~n", [Result]),
        case Result of
            {ok, UpdatedConfig} ->
                io:format("Config updated successfully~n"),
                json_response(200, UpdatedConfig, Req1, State);
            {error, Reason} ->
                io:format("Config update failed: ~p~n", [Reason]),
                json_response(400, #{status => error, reason => Reason}, Req1, State)
        end
    catch
        Type:What ->
            io:format("Error processing config update: ~p:~p~nBody: ~p~n", 
                     [Type, What, Body]),
            json_response(400, #{status => error, reason => invalid_json}, Req1, State)
    end;

handle_request(_, _, Req, State) ->
    json_response(404, #{status => error, reason => not_found}, Req, State).

json_response(Status, Body, Req, State) ->
    try
        EncodedBody = jsx:encode(Body),
        io:format("Sending response: Status=~p, Body=~p~n", [Status, Body]),
        FinalReq = cowboy_req:reply(Status, #{
            <<"content-type">> => <<"application/json">>
        }, EncodedBody, Req),
        {ok, FinalReq, State}
    catch
        ErrorType:ErrorReason ->
            io:format("Error encoding response JSON: ~p:~p~nBody: ~p~n", 
                     [ErrorType, ErrorReason, Body]),
            ErrorReq = cowboy_req:reply(500, #{
                <<"content-type">> => <<"application/json">>
            }, jsx:encode(#{status => error, reason => json_encode_failed}), Req),
            {ok, ErrorReq, State}
    end.
