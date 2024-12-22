-- Connect to the database
\c smsc_db;

-- Create enum types for message status
CREATE TYPE message_status AS ENUM (
    'pending',
    'sent',
    'delivered',
    'failed',
    'cancelled'
);

-- Create table for SMSC configuration
CREATE TABLE IF NOT EXISTS smsc_config (
    key VARCHAR(255) PRIMARY KEY,
    value JSONB NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- Create table for messages
CREATE TABLE IF NOT EXISTS smsc_messages (
    id VARCHAR(255) PRIMARY KEY,
    content TEXT NOT NULL,
    priority INTEGER NOT NULL DEFAULT 1,
    status message_status NOT NULL DEFAULT 'pending',
    retries INTEGER DEFAULT 0,
    error_message TEXT,
    source_addr VARCHAR(255),
    dest_addr VARCHAR(255),
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    scheduled_at TIMESTAMP WITH TIME ZONE,
    sent_at TIMESTAMP WITH TIME ZONE,
    delivered_at TIMESTAMP WITH TIME ZONE
);

-- Create table for message status history
CREATE TABLE IF NOT EXISTS message_status_history (
    id SERIAL PRIMARY KEY,
    message_id VARCHAR(255) REFERENCES smsc_messages(id),
    old_status message_status,
    new_status message_status NOT NULL,
    error_message TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- Create table for metrics
CREATE TABLE IF NOT EXISTS smsc_metrics (
    id SERIAL PRIMARY KEY,
    metric_name VARCHAR(255) NOT NULL,
    metric_value JSONB NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- Create indexes
CREATE INDEX idx_messages_status ON smsc_messages(status);
CREATE INDEX idx_messages_created_at ON smsc_messages(created_at);
CREATE INDEX idx_messages_scheduled_at ON smsc_messages(scheduled_at);
CREATE INDEX idx_status_history_message_id ON message_status_history(message_id);
CREATE INDEX idx_metrics_name ON smsc_metrics(metric_name);
CREATE INDEX idx_metrics_created_at ON smsc_metrics(created_at);

-- Create function to update updated_at timestamp
CREATE OR REPLACE FUNCTION update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = CURRENT_TIMESTAMP;
    RETURN NEW;
END;
$$ language 'plpgsql';

-- Create triggers for updated_at
CREATE TRIGGER update_smsc_config_updated_at
    BEFORE UPDATE ON smsc_config
    FOR EACH ROW
    EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_smsc_messages_updated_at
    BEFORE UPDATE ON smsc_messages
    FOR EACH ROW
    EXECUTE FUNCTION update_updated_at_column();

-- Insert default configuration
INSERT INTO smsc_config (key, value) VALUES
('smsc', '{
    "smsc_host": "localhost",
    "smsc_port": 2775,
    "system_id": "test_system",
    "password": "test_password",
    "system_type": "",
    "interface_version": 52,
    "enquire_link_interval": 30,
    "reconnect_interval": 5,
    "max_retries": 3,
    "retry_delay": 60
}'::jsonb)
ON CONFLICT (key) DO UPDATE
SET value = EXCLUDED.value;

-- Create view for message statistics
CREATE OR REPLACE VIEW message_statistics AS
SELECT
    COUNT(*) as total_messages,
    COUNT(*) FILTER (WHERE status = 'pending') as pending_messages,
    COUNT(*) FILTER (WHERE status = 'sent') as sent_messages,
    COUNT(*) FILTER (WHERE status = 'delivered') as delivered_messages,
    COUNT(*) FILTER (WHERE status = 'failed') as failed_messages,
    COUNT(*) FILTER (WHERE status = 'cancelled') as cancelled_messages,
    COUNT(*) FILTER (WHERE created_at > NOW() - INTERVAL '1 hour') as messages_last_hour,
    COUNT(*) FILTER (WHERE created_at > NOW() - INTERVAL '24 hours') as messages_last_day
FROM smsc_messages;

-- Create function to record message status changes
CREATE OR REPLACE FUNCTION record_message_status_change()
RETURNS TRIGGER AS $$
BEGIN
    IF (TG_OP = 'UPDATE' AND OLD.status IS DISTINCT FROM NEW.status) THEN
        INSERT INTO message_status_history
            (message_id, old_status, new_status, error_message)
        VALUES
            (NEW.id, OLD.status, NEW.status, NEW.error_message);
    END IF;
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

-- Create trigger for message status changes
CREATE TRIGGER message_status_change_trigger
    AFTER UPDATE ON smsc_messages
    FOR EACH ROW
    EXECUTE FUNCTION record_message_status_change();

-- Grant permissions to smsc_user
GRANT ALL PRIVILEGES ON ALL TABLES IN SCHEMA public TO smsc_user;
GRANT ALL PRIVILEGES ON ALL SEQUENCES IN SCHEMA public TO smsc_user;
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA public TO smsc_user;
