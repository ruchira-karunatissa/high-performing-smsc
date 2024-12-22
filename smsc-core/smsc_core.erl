%%%-------------------------------------------------------------------
%%% @doc
%%% SMSC Core Application
%%% @end
%%%-------------------------------------------------------------------
-module(smsc_core).
-behaviour(application).

%% Application exports
-export([start/2, stop/1]).

%% API exports
-export([submit_message/1, query_message/1, cancel_message/1,
         get_config/1, update_config/2,
         get_metrics/0, get_system_status/0]).

%%====================================================================
%% Application callbacks
%%====================================================================

start(_StartType, _StartArgs) ->
    smsc_sup:start_link().

stop(_State) ->
    ok.

%%====================================================================
%% API functions
%%====================================================================

submit_message(Params) ->
    gen_server:call(smsc_server, {submit_message, Params}).

query_message(MessageId) ->
    gen_server:call(smsc_server, {query_message, MessageId}).

cancel_message(MessageId) ->
    gen_server:call(smsc_server, {cancel_message, MessageId}).

get_config(Section) ->
    gen_server:call(smsc_server, {get_config, Section}).

update_config(Section, NewConfig) ->
    gen_server:call(smsc_server, {update_config, Section, NewConfig}).

get_metrics() ->
    gen_server:call(smsc_server, get_metrics).

get_system_status() ->
    gen_server:call(smsc_server, get_system_status).
