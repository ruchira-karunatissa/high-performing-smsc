{application, smsc_core, [
    {description, "SMSC Core Implementation"},
    {vsn, "0.1.0"},
    {registered, [smsc_sup, smsc_server]},
    {mod, {smsc_core, []}},
    {applications, [
        kernel,
        stdlib,
        sasl,
        crypto,
        ranch,
        cowlib,
        cowboy,
        jsx
    ]},
    {env, [
        {smsc_host, "localhost"},
        {smsc_port, 2775},
        {system_id, "test_system"},
        {password, "test_password"},
        {system_type, ""},
        {interface_version, 52},
        {http_port, 8080}
    ]},
    {modules, [smsc_core, smsc_sup, smsc_server, smsc_http_handler, smsc_db]}
]}.
