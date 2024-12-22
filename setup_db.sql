CREATE DATABASE smsc_db;
\c smsc_db;

CREATE USER smsc_user WITH PASSWORD 'smsc_password';
GRANT ALL PRIVILEGES ON DATABASE smsc_db TO smsc_user;

-- Create the config table
CREATE TABLE smsc_config (
    key TEXT PRIMARY KEY,
    value JSONB NOT NULL
);

-- Insert default SMSC configuration
INSERT INTO smsc_config (key, value) VALUES (
    'smsc_config',
    '{
        "smsc_host": "localhost",
        "smsc_port": 2775,
        "system_id": "test_system",
        "password": "test_password",
        "max_retries": 3,
        "retry_delay": 60,
        "system_type": "",
        "interface_version": 52,
        "reconnect_interval": 5,
        "enquire_link_interval": 30
    }'::jsonb
);

-- Grant permissions to smsc_user
GRANT ALL PRIVILEGES ON TABLE smsc_config TO smsc_user;
