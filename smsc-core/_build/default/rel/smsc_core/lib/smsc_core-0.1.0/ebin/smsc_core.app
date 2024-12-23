{application,smsc_core,
             [{description,"SMSC Core Implementation"},
              {vsn,"0.1.0"},
              {registered,[smsc_sup,smsc_server]},
              {mod,{smsc_core,[]}},
              {applications,[kernel,stdlib,sasl,crypto,ranch,cowlib,cowboy,
                             jsx,epgsql]},
              {env,[{smsc_host,"localhost"},
                    {smsc_port,2775},
                    {system_id,"test_system"},
                    {password,"test_password"},
                    {system_type,[]},
                    {interface_version,52},
                    {http_port,8080},
                    {postgres_host,"localhost"},
                    {postgres_port,5432},
                    {postgres_database,"smsc_db"},
                    {postgres_user,"smsc_user"},
                    {postgres_password,"smsc_password"}]},
              {modules,[smsc_core,smsc_db,smsc_http_handler,smsc_server,
                        smsc_sup,smsc_utils]},
              {licenses,["Apache 2.0"]},
              {links,[]}]}.
