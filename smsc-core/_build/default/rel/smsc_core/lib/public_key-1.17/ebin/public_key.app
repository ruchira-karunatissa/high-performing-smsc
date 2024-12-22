{application, public_key,
  [{description, "Public key infrastructure"},
   {vsn, "1.17"},
   {modules, [public_key,
              pubkey_pem,
              pubkey_pbe,
              pubkey_ssh,
              pubkey_cert,
              pubkey_policy_tree,
              pubkey_cert_records,
              pubkey_crl,
              pubkey_ocsp,
              pubkey_os_cacerts,
              'OTP-PUB-KEY',
              'PKCS-FRAME'
             ]},
   {applications, [asn1, crypto, kernel, stdlib]},
   {registered, []},
   {env, []},
   {runtime_dependencies, ["stdlib-4.0","kernel-8.0","erts-13.0",
                           "crypto-5.0","asn1-5.0"]}
  ]
}.
