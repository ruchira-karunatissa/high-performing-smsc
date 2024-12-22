running the smsc-core backend in cmd:

escript rebar3 shell

in the erlan shell:

cd("src").
c(smsc_db).
c(smsc_server).
c(smsc_http_handler).
cd("..").
smsc_utils:restart().

