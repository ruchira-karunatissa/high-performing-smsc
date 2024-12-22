# SMSC Core Application Design Document

## Table of Contents
1. [Overview](#overview)
2. [Solution Architecture](#solution-architecture)
3. [Component Design](#component-design)
4. [Database Design](#database-design)
5. [API Design](#api-design)
6. [Deployment Architecture](#deployment-architecture)
7. [Performance Considerations](#performance-considerations)
8. [Security Considerations](#security-considerations)
9. [Monitoring and Logging](#monitoring-and-logging)
10. [Future Improvements](#future-improvements)
11. [SMPP Integration Design](#smpp-integration-design)

## Overview

The SMSC application consists of two main components:
1. **SMSC Core** - An Erlang-based SMS Center implementation that handles SMS message routing, delivery, and management
2. **SMSC Frontend** - A React-based web application that provides a user interface for configuration, monitoring, and message management

### Key Features
- Message submission and routing
- Configuration management
- Message status tracking
- Performance metrics
- SMPP protocol support
- REST API interface
- Web-based administration interface
- Real-time monitoring dashboard
- Message queue visualization

## Solution Architecture

### High-Level Architecture
```
                    +------------------+
                    |                  |
                    |    Keycloak      |
                    |    (Auth)        |
                    |                  |
                    +------------------+
                           ↑↓
                    +------------------+     +------------------+     +------------------+     +------------------+
                    |                  |     |                  |     |                  |     |                  |
                    |  SMSC Frontend   |     |  API Layer      |     |  SMSC Core      |     |  External       |
                    |  (React)         |---->|  (REST/WS)      |---->|  (Erlang)       |---->|  SMSC           |
                    |                  |     |                  |     |                  |     |  (SMPP)         |
                    +------------------+     +------------------+     +------------------+     +------------------+
                           |                       |                       |                         
                           |                       |                       |                         
                           v                       v                       v                         
                    +------------------+     +------------------+     +------------------+     
                    |                  |     |                  |     |                  |     
                    |  User Interface  |     |  API Endpoints   |     |  Erlang         |     
                    |  Components      |     |  & WebSocket     |     |  Message Queue  |     
                    |                  |     |                  |     |                  |     
                    +------------------+     +------------------+     +------------------+     
                           |                       |                       |                         
                           |                       |                       |                         
                           v                       v                       v                         
                    +------------------+     +------------------+     
                    |                  |     |                  |     
                    |  State           |     |  Database        |     
                    |  Management      |     |  (PostgreSQL)    |<-----------------+
                    |                  |     |                  |                   |
                    +------------------+     +------------------+                   |
                                                                                  |
                                                                    Direct DB Connection
```

### Frontend Architecture
```
+-------------------+     +-------------------+     +-------------------+
|                   |     |                   |     |                   |
|  React Components |     |  Redux Store      |     |  API Services    |
|  & Pages          |<--->|  & Middleware     |<--->|  & Interceptors  |
|                   |     |                   |     |                   |
+-------------------+     +-------------------+     +-------------------+
         |                        |                          |
         v                        v                          v
+-------------------+     +-------------------+     +-------------------+
|                   |     |                   |     |                   |
|  UI Components    |     |  State Management |     |  WebSocket       |
|  Library          |     |  & Actions        |     |  Connection      |
|                   |     |                   |     |                   |
+-------------------+     +-------------------+     +-------------------+
```

## Component Design

### Component Responsibilities

#### Keycloak
- User authentication
- Identity management
- Role-based access control
- OAuth2/OpenID Connect
- Single Sign-On (SSO)
- User session management

#### SMSC Frontend
- Web-based user interface
- Integration with Keycloak for auth
- Real-time monitoring displays
- Configuration management
- Message status tracking
- Performance metrics visualization

#### API Layer
- REST API endpoints
- WebSocket connections
- JWT token validation
- Request validation
- Rate limiting
- Request/Response transformation

#### SMSC Core
- SMPP protocol handling
- Message queuing using Erlang message queue
- Direct database operations via PostgreSQL driver
- Performance metrics collection
- Error handling and recovery
- Connection management with external SMSC

#### Erlang Message Queue
- Internal message queue for SMPP operations
- Handles message routing between processes
- Provides buffering for SMPP operations
- Manages message priorities
- Part of Erlang/OTP supervision tree

#### Database (PostgreSQL)
- Direct connection from SMSC Core
- Message storage and retrieval
- Configuration data
- System metrics
- Performance logs
- Queue status

### Data Flow
1. Frontend makes authenticated HTTP/WebSocket requests to API Layer
2. API Layer validates JWT token
3. API Layer forwards valid requests to SMSC Core
4. SMSC Core:
   - Uses internal Erlang message queue for SMPP operations
   - Directly connects to PostgreSQL for data operations
5. Core manages SMPP connections with External SMSC
6. API Layer streams updates back to Frontend
7. Frontend displays real-time updates

### Frontend Module Structure
```
smsc-frontend/
├── src/
│   ├── components/           # Reusable UI components
│   │   ├── Dashboard/
│   │   ├── Messages/
│   │   ├── Configuration/
│   │   └── common/
│   ├── pages/               # Page components
│   │   ├── Home/
│   │   ├── Messages/
│   │   ├── Config/
│   │   └── Metrics/
│   ├── store/               # Redux store configuration
│   │   ├── actions/
│   │   ├── reducers/
│   │   └── middleware/
│   ├── services/            # API services
│   │   ├── api.js
│   │   ├── websocket.js
│   │   └── interceptors.js
│   ├── utils/               # Utility functions
│   └── App.js              # Root component
├── public/
└── package.json
```

### Backend Module Structure
```
smsc_core/
├── src/
│   ├── smsc_app.erl           # Application entry point
│   ├── smsc_sup.erl           # Supervisor
│   ├── smsc_server.erl        # Core server implementation
│   ├── smsc_http_handler.erl  # HTTP API handlers
│   ├── smsc_db.erl           # Database interface
│   ├── smsc_utils.erl        # Utility functions
│   └── smsc_metrics.erl      # Metrics collection
├── include/
│   └── smsc.hrl             # Common definitions
└── priv/
    └── schema/              # Database schemas
```

## Database Design

### Entity Relationship Diagram
```
+---------------+     +------------------+     +----------------+
|    Config     |     |     Messages     |     |    Metrics     |
+---------------+     +------------------+     +----------------+
| PK key        |     | PK id           |     | PK id          |
|    value      |     |    source_addr  |     |    timestamp   |
|    created_at |     |    dest_addr    |     |    name        |
|    updated_at |     |    message_text |     |    value       |
|               |     |    status       |     |    type        |
|               |     |    created_at   |     |                |
|               |     |    updated_at   |     |                |
|               |     |    retry_count  |     |                |
|               |     | FK config_id    |     | FK message_id  |
+---------------+     +------------------+     +----------------+
```

### Table Definitions

#### Config Table
```sql
CREATE TABLE smsc_config (
    key TEXT PRIMARY KEY,
    value JSONB NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- Trigger to update timestamp
CREATE TRIGGER update_config_timestamp
    BEFORE UPDATE ON smsc_config
    FOR EACH ROW
    EXECUTE FUNCTION update_timestamp();
```

#### Messages Table
```sql
CREATE TABLE smsc_messages (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    source_addr TEXT NOT NULL,
    dest_addr TEXT NOT NULL,
    message_text TEXT NOT NULL,
    status TEXT NOT NULL CHECK (status IN ('pending', 'sent', 'failed', 'delivered', 'expired')),
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    retry_count INTEGER DEFAULT 0,
    config_id TEXT REFERENCES smsc_config(key),
    payload JSONB,
    error_message TEXT,
    scheduled_at TIMESTAMP WITH TIME ZONE,
    expires_at TIMESTAMP WITH TIME ZONE,
    delivery_report JSONB
);

-- Indexes
CREATE INDEX idx_messages_status ON smsc_messages(status);
CREATE INDEX idx_messages_created_at ON smsc_messages(created_at);
CREATE INDEX idx_messages_source_addr ON smsc_messages(source_addr);
CREATE INDEX idx_messages_dest_addr ON smsc_messages(dest_addr);
```

#### Metrics Table
```sql
CREATE TABLE smsc_metrics (
    id BIGSERIAL PRIMARY KEY,
    timestamp TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    name TEXT NOT NULL,
    value NUMERIC NOT NULL,
    type TEXT NOT NULL CHECK (type IN ('counter', 'gauge', 'histogram')),
    message_id UUID REFERENCES smsc_messages(id),
    labels JSONB
);

-- Indexes
CREATE INDEX idx_metrics_timestamp ON smsc_metrics(timestamp);
CREATE INDEX idx_metrics_name ON smsc_metrics(name);
```

### Database Functions

#### Update Timestamp Function
```sql
CREATE OR REPLACE FUNCTION update_timestamp()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = CURRENT_TIMESTAMP;
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;
```

#### Message Status Update Function
```sql
CREATE OR REPLACE FUNCTION update_message_status(
    p_message_id UUID,
    p_status TEXT,
    p_error_message TEXT DEFAULT NULL
)
RETURNS VOID AS $$
BEGIN
    UPDATE smsc_messages
    SET status = p_status,
        error_message = p_error_message,
        updated_at = CURRENT_TIMESTAMP
    WHERE id = p_message_id;
END;
$$ LANGUAGE plpgsql;
```

### Database Views

#### Message Statistics View
```sql
CREATE VIEW message_statistics AS
SELECT 
    status,
    COUNT(*) as count,
    AVG(EXTRACT(EPOCH FROM (updated_at - created_at))) as avg_processing_time
FROM smsc_messages
WHERE created_at > CURRENT_TIMESTAMP - INTERVAL '24 hours'
GROUP BY status;
```

#### Active Configurations View
```sql
CREATE VIEW active_configurations AS
SELECT 
    key,
    value,
    updated_at
FROM smsc_config
WHERE (value->>'active')::boolean = true;
```

## API Design

### REST API

#### Message Operations

##### Submit Message
```yaml
POST /api/messages
Request:
  Content-Type: application/json
  Body:
    {
      "source_addr": "string",
      "dest_addr": "string",
      "message_text": "string",
      "scheduled_at": "string (ISO 8601)",
      "expires_at": "string (ISO 8601)",
      "options": {
        "priority": "number",
        "validity_period": "number",
        "callback_url": "string"
      }
    }
Response:
  200:
    {
      "status": "success",
      "data": {
        "message_id": "uuid",
        "status": "pending"
      }
    }
  400:
    {
      "status": "error",
      "error": {
        "code": "string",
        "message": "string"
      }
    }
```

##### Get Message Status
```yaml
GET /api/messages/{id}
Response:
  200:
    {
      "status": "success",
      "data": {
        "message_id": "uuid",
        "source_addr": "string",
        "dest_addr": "string",
        "status": "string",
        "created_at": "string",
        "updated_at": "string",
        "delivery_report": {}
      }
    }
  404:
    {
      "status": "error",
      "error": {
        "code": "not_found",
        "message": "Message not found"
      }
    }
```

##### List Messages
```yaml
GET /api/messages
Parameters:
  - status: string
  - source_addr: string
  - dest_addr: string
  - from_date: string
  - to_date: string
  - page: number
  - limit: number
Response:
  200:
    {
      "status": "success",
      "data": {
        "items": [],
        "pagination": {
          "page": 1,
          "limit": 10,
          "total": 100
        }
      }
    }
```

#### Configuration Operations

##### Get Configuration
```yaml
GET /api/config
Response:
  200:
    {
      "status": "success",
      "data": {
        "smsc_host": "string",
        "smsc_port": "number",
        "system_id": "string",
        "password": "string",
        "system_type": "string",
        "interface_version": "number",
        "reconnect_interval": "number",
        "enquire_link_interval": "number"
      }
    }
```

##### Update Configuration
```yaml
POST /api/config
Request:
  Content-Type: application/json
  Body:
    {
      "smsc_host": "string",
      "smsc_port": "number",
      "system_id": "string",
      "password": "string",
      "system_type": "string",
      "interface_version": "number",
      "reconnect_interval": "number",
      "enquire_link_interval": "number"
    }
Response:
  200:
    {
      "status": "success",
      "data": {
        "updated": true
      }
    }
```

#### Metrics Operations

##### Get Metrics
```yaml
GET /api/metrics
Parameters:
  - type: string
  - from: string
  - to: string
Response:
  200:
    {
      "status": "success",
      "data": {
        "message_counts": {
          "total": "number",
          "pending": "number",
          "sent": "number",
          "failed": "number",
          "delivered": "number"
        },
        "performance": {
          "messages_per_second": "number",
          "average_response_time": "number"
        },
        "system": {
          "cpu_usage": "number",
          "memory_usage": "number",
          "queue_size": "number"
        }
      }
    }
```

### WebSocket API

#### Connection
```yaml
WebSocket URL: ws://localhost:8080/ws
Connection Parameters:
  - token: string (JWT authentication token)
```

#### Message Events
```yaml
# Message Status Update
{
  "type": "message_status",
  "data": {
    "message_id": "uuid",
    "status": "string",
    "timestamp": "string"
  }
}

# Metrics Update
{
  "type": "metrics_update",
  "data": {
    "timestamp": "string",
    "metrics": {
      "queue_size": "number",
      "messages_per_second": "number",
      "active_connections": "number"
    }
  }
}

# System Alert
{
  "type": "system_alert",
  "data": {
    "level": "string",
    "message": "string",
    "timestamp": "string"
  }
}
```

### Error Codes
```yaml
Common Error Codes:
  - invalid_request: 400
  - unauthorized: 401
  - forbidden: 403
  - not_found: 404
  - rate_limit_exceeded: 429
  - internal_error: 500

Domain-Specific Error Codes:
  - message_expired: 4001
  - invalid_destination: 4002
  - queue_full: 4003
  - connection_failed: 5001
  - delivery_failed: 5002
```

## Deployment Architecture

### Production Deployment
```
+------------------+     +------------------+
|                  |     |                  |
|  CDN             |     |  Load Balancer   |
|  (Frontend)      |     |  (API/SMPP)      |
|                  |     |                  |
+------------------+     +------------------+
         |                       |
         |                       |
         v                       v
+------------------+     +------------------+
|                  |     |                  |
|  React App       |     |  SMSC Core      |
|  (Static)        |     |  Cluster        |
|                  |     |                  |
+------------------+     +------------------+
         |                       |
         |                       |
         v                       v
+------------------+     +------------------+
|                  |     |                  |
|  Browser Cache   |     |  PostgreSQL      |
|  & Storage       |     |  Cluster         |
|                  |     |                  |
+------------------+     +------------------+
         |                       |
         |                       |
         v                       v
+------------------+     +------------------+
|                  |     |                  |
|  Service Worker  |     |  Monitoring &    |
|  (PWA)           |     |  Logging         |
|                  |     |                  |
+------------------+     +------------------+
```

### Deployment Requirements

#### Frontend
- Node.js 16 or later
- NPM or Yarn
- Static file hosting (CDN)
- SSL certificate
- Service worker support

#### Backend
- Erlang/OTP 24 or later
- PostgreSQL 12 or later
- Minimum 4GB RAM per instance
- Load balancer with SSL termination
- Monitoring and logging infrastructure

## Performance Considerations

### Connection Pooling
- Database connection pool size: `{pool_size, 10}`
- SMPP connection pool size: Based on throughput
- HTTP connection pool size: Based on concurrent requests

### Caching
- Configuration caching with TTL
- Message status caching
- Connection state caching

### Optimizations
- Batch message processing
- Asynchronous message delivery
- Connection keep-alive
- Query optimization

## Security Considerations

### Authentication & Authorization
- API key authentication
- Role-based access control
- SSL/TLS encryption

### Data Security
- Encrypted database connections
- Secure configuration storage
- Audit logging

### Network Security
- Firewall rules
- Rate limiting
- DDoS protection

## Monitoring and Logging

### SMSC Core Monitoring Design

#### Core System Metrics
```
+------------------+     +------------------+     +------------------+
|                  |     |                  |     |                  |
|  SMSC Core       |     |  Metrics         |     |  Dashboard      |
|  Components      |---->|  Collector       |---->|  Display        |
|                  |     |                  |     |                  |
+------------------+     +------------------+     +------------------+
```

#### Monitored Components

##### Message Processing
```yaml
Queue Metrics:
  - queue_length
  - processing_rate
  - average_processing_time
  - retry_queue_size

Message Stats:
  - messages_received
  - messages_processed
  - messages_failed
  - messages_pending
```

##### System Performance
```yaml
Resource Usage:
  - cpu_utilization
  - memory_usage
  - disk_io
  - network_bandwidth

Database Metrics:
  - connection_pool_status
  - query_response_time
  - active_transactions
  - deadlock_count
```

##### Error Monitoring
```yaml
System Errors:
  - process_crashes
  - supervisor_restarts
  - database_errors
  - memory_alerts

Message Errors:
  - parsing_failures
  - routing_errors
  - database_write_failures
  - timeout_errors
```

#### Dashboard Views

##### System Health Overview
```
+------------------------+     +------------------------+
|                        |     |                        |
|  System Status         |     |  Message Queue Status  |
|  - Process Status      |     |  - Queue Length       |
|  - Resource Usage      |     |  - Processing Rate    |
|  - Error Rate         |     |  - Success Rate       |
|                        |     |                        |
+------------------------+     +------------------------+
```

##### Performance Metrics
```typescript
interface CorePerformanceMetrics {
    messageProcessing: {
        received: number;
        processed: number;
        failed: number;
        pending: number;
        processingRate: number;
    };
    systemResources: {
        cpuUsage: number;
        memoryUsage: number;
        diskIO: number;
        networkIO: number;
    };
    database: {
        connectionStatus: boolean;
        activeConnections: number;
        queryLatency: number;
    };
}
```

##### Error Tracking
```typescript
interface CoreErrorMetrics {
    system: {
        type: string;
        count: number;
        lastOccurrence: Date;
        processName: string;
    }[];
    messages: {
        type: string;
        count: number;
        details: string;
    }[];
}
```

#### Alert Configuration

##### System Alerts
```yaml
Critical Alerts:
  - process_crash:
      threshold: any occurrence
      action: restart_process
  - memory_usage:
      threshold: >90%
      interval: 1 minute
  - database_connection:
      threshold: connection_lost
      action: reconnect

Warning Alerts:
  - high_queue_length:
      threshold: >1000 messages
      interval: 5 minutes
  - processing_delay:
      threshold: >5 seconds
      interval: 1 minute
  - error_rate:
      threshold: >5%
      interval: 5 minutes
```

#### Metric Collection
```erlang
-record(core_metrics, {
    timestamp :: integer(),
    queue_length :: integer(),
    processing_rate :: float(),
    cpu_usage :: float(),
    memory_usage :: float(),
    error_count :: integer(),
    active_processes :: integer()
}).

collect_core_metrics() ->
    Metrics = #core_metrics{
        timestamp = os:system_time(millisecond),
        queue_length = get_queue_length(),
        processing_rate = calculate_processing_rate(),
        cpu_usage = get_cpu_usage(),
        memory_usage = get_memory_usage(),
        error_count = get_error_count(),
        active_processes = get_process_count()
    },
    store_core_metrics(Metrics).
```

#### Metric Storage
```sql
CREATE TABLE smsc_core_metrics (
    id BIGSERIAL PRIMARY KEY,
    timestamp TIMESTAMP WITH TIME ZONE NOT NULL,
    queue_length INTEGER NOT NULL,
    processing_rate FLOAT NOT NULL,
    cpu_usage FLOAT NOT NULL,
    memory_usage FLOAT NOT NULL,
    error_count INTEGER NOT NULL,
    active_processes INTEGER NOT NULL
);

CREATE INDEX idx_core_metrics_timestamp ON smsc_core_metrics(timestamp);
```

## Future Improvements

### Short Term
1. Implement proper connection pooling
2. Add comprehensive metrics
3. Improve error handling
4. Add request validation

### Medium Term
1. Add support for multiple SMSC connections
2. Implement message prioritization
3. Add support for message templates
4. Implement rate limiting

### Long Term
1. Add support for clustering
2. Implement automatic failover
3. Add support for message routing rules
4. Implement advanced monitoring

## SMPP Integration Design

### SMPP Client Architecture
```
+------------------+     +------------------+     +------------------+
|                  |     |                  |     |                  |
|  SMSC Core       |     |  SMPP Client     |     |  External       |
|  Server          |---->|  Pool            |---->|  SMSC           |
|                  |     |                  |     |                  |
+------------------+     +------------------+     +------------------+
         |                       |                         |
         |                       |                         |
         v                       v                         v
+------------------+     +------------------+     +------------------+
|                  |     |                  |     |                  |
|  Message         |     |  Connection      |     |  Delivery       |
|  Queue           |     |  Manager         |     |  Reports        |
|                  |     |                  |     |                  |
+------------------+     +------------------+     +------------------+
         |                       |                         |
         |                       |                         |
         v                       v                         v
+------------------+     +------------------+     +------------------+
|                  |     |                  |     |                  |
|  Metrics         |     |  State           |     |  Error          |
|  Collector       |     |  Monitor         |     |  Handler        |
|                  |     |                  |     |                  |
+------------------+     +------------------+     +------------------+
```

### SMPP Connection Management

#### Connection Pool
```erlang
-record(smpp_connection, {
    id :: binary(),
    host :: string(),
    port :: integer(),
    system_id :: string(),
    password :: string(),
    state :: connected | disconnected | error,
    last_activity :: integer(),
    error_count :: integer(),
    metrics :: map()
}).

-record(connection_pool, {
    max_size :: integer(),
    active_connections :: [#smpp_connection{}],
    waiting_queue :: queue:queue(),
    metrics :: map()
}).
```

#### Connection States
```
                    +-------------+
                    |             |
                    |   INIT      |
                    |             |
                    +-------------+
                          |
                          v
                    +-------------+
            +------>|             |
            |       |  CONNECTING |
            |       |             |
            |       +-------------+
            |             |
            |             v
            |       +-------------+
            |       |             |
     Failure|       | CONNECTED   |
            |       |             |
            |       +-------------+
            |             |
            |             v
            |       +-------------+
            |       |             |
            +-------| RECONNECTING|
                    |             |
                    +-------------+
```

### Monitoring Integration

#### Metric Collection Architecture
```
+------------------+     +------------------+     +------------------+
|                  |     |                  |     |                  |
|  SMPP Client     |     |  Metrics         |     |  Monitoring     |
|  Events          |---->|  Collector       |---->|  Dashboard      |
|                  |     |                  |     |                  |
+------------------+     +------------------+     +------------------+
         |                       |                         |
         |                       |                         |
         v                       v                         v
+------------------+     +------------------+     +------------------+
|                  |     |                  |     |                  |
|  Performance     |     |  Time Series     |     |  Real-time      |
|  Metrics         |     |  Database        |     |  Updates        |
|                  |     |                  |     |                  |
+------------------+     +------------------+     +------------------+
```

#### Metrics Types

##### SMPP Metrics
```yaml
Connection Metrics:
  - bind_count
  - bind_duration
  - connection_errors
  - reconnection_attempts
  - active_connections

Message Metrics:
  - submit_sm_count
  - deliver_sm_count
  - message_errors
  - throughput
  - latency

Session Metrics:
  - enquire_link_latency
  - window_size
  - sequence_number_state
```

##### System Metrics
```yaml
Resource Metrics:
  - cpu_usage
  - memory_usage
  - disk_usage
  - network_io

Queue Metrics:
  - queue_size
  - queue_latency
  - processing_time
  - retry_count

Error Metrics:
  - error_count_by_type
  - error_rate
  - recovery_time
```

### Monitoring Dashboard Design

#### Real-time Monitoring View
```
+------------------------+     +------------------------+
|                        |     |                        |
|  Connection Status     |     |  Message Queue Status  |
|  - Active Sessions     |     |  - Pending Messages   |
|  - Bind State         |     |  - Processing Rate    |
|  - Error Rate         |     |  - Success Rate       |
|                        |     |                        |
+------------------------+     +------------------------+
|                        |     |                        |
|  Performance Metrics   |     |  System Health         |
|  - Throughput         |     |  - CPU Usage          |
|  - Latency            |     |  - Memory Usage       |
|  - Success Rate       |     |  - Disk I/O           |
|                        |     |                        |
+------------------------+     +------------------------+
```

#### Dashboard Components

##### Connection Monitor
```typescript
interface ConnectionStatus {
    id: string;
    state: 'connected' | 'disconnected' | 'error';
    uptime: number;
    lastActivity: Date;
    errorCount: number;
    metrics: {
        throughput: number;
        latency: number;
        windowSize: number;
    };
}

interface ConnectionMonitor extends React.Component {
    state: {
        connections: ConnectionStatus[];
        alerts: Alert[];
        statistics: {
            totalConnections: number;
            activeConnections: number;
            errorRate: number;
        };
    };
}
```

##### Message Queue Monitor
```typescript
interface QueueMetrics {
    size: number;
    processingRate: number;
    averageLatency: number;
    errorRate: number;
    retryCount: number;
}

interface QueueMonitor extends React.Component {
    state: {
        metrics: QueueMetrics;
        history: {
            timestamp: Date;
            metrics: QueueMetrics;
        }[];
    };
}
```

##### Performance Dashboard
```typescript
interface PerformanceMetrics {
    messageCount: {
        total: number;
        success: number;
        failed: number;
        pending: number;
    };
    throughput: {
        current: number;
        average: number;
        peak: number;
    };
    latency: {
        p50: number;
        p90: number;
        p99: number;
    };
}

interface PerformanceDashboard extends React.Component {
    state: {
        realtime: PerformanceMetrics;
        historical: {
            timestamp: Date;
            metrics: PerformanceMetrics;
        }[];
    };
}
```

### Alert System

#### Alert Types
```yaml
Connection Alerts:
  - connection_lost
  - bind_failed
  - high_error_rate
  - reconnection_failed

Performance Alerts:
  - high_latency
  - low_throughput
  - queue_overflow
  - message_timeout

System Alerts:
  - high_cpu_usage
  - memory_pressure
  - disk_space_low
  - network_issues
```

#### Alert Integration
```typescript
interface Alert {
    id: string;
    type: AlertType;
    severity: 'info' | 'warning' | 'error' | 'critical';
    message: string;
    timestamp: Date;
    metadata: Record<string, any>;
}

interface AlertSystem {
    subscribe(callback: (alert: Alert) => void): void;
    unsubscribe(callback: (alert: Alert) => void): void;
    acknowledge(alertId: string): Promise<void>;
    mute(alertType: AlertType, duration: number): void;
}
```

### WebSocket Integration

#### Real-time Updates
```typescript
interface WebSocketMessage {
    type: 'metrics' | 'alert' | 'status';
    data: {
        timestamp: Date;
        payload: any;
    };
}

class MetricsWebSocket {
    private ws: WebSocket;
    private reconnectAttempts: number = 0;
    
    connect() {
        this.ws = new WebSocket('ws://localhost:8080/metrics');
        this.ws.onmessage = this.handleMessage;
        this.ws.onclose = this.handleDisconnect;
    }
    
    private handleMessage(event: MessageEvent) {
        const message: WebSocketMessage = JSON.parse(event.data);
        store.dispatch(updateMetrics(message));
    }
}
```

### Authentication Flow
1. User accesses SMSC Frontend
2. Frontend redirects to Keycloak login
3. User authenticates with Keycloak
4. Keycloak issues JWT token
5. Frontend stores token
6. API requests include JWT token
7. API Layer validates token
8. Token refresh handled automatically

### Security Considerations

#### Token Management
```typescript
interface AuthToken {
    access_token: string;
    refresh_token: string;
    expires_in: number;
    token_type: string;
    scope: string;
}

class TokenManager {
    private refreshTokenTimeout: NodeJS.Timeout;

    storeToken(token: AuthToken) {
        localStorage.setItem('auth_token', token.access_token);
        this.scheduleTokenRefresh(token.expires_in);
    }

    private scheduleTokenRefresh(expiresIn: number) {
        // Refresh 1 minute before expiry
        const refreshTime = (expiresIn - 60) * 1000;
        this.refreshTokenTimeout = setTimeout(
            () => this.refreshToken(),
            refreshTime
        );
    }
}
```

#### API Security
```typescript
// API request interceptor
axios.interceptors.request.use(config => {
    const token = localStorage.getItem('auth_token');
    if (token) {
        config.headers.Authorization = `Bearer ${token}`;
    }
    return config;
});

// WebSocket security
class SecureWebSocket {
    connect() {
        const token = localStorage.getItem('auth_token');
        this.ws = new WebSocket(
            `ws://localhost:8080/ws?token=${token}`
        );
    }
}
```

#### Role-Based Access
```typescript
interface UserRole {
    role: 'admin' | 'operator' | 'viewer';
    permissions: string[];
}

const rolePermissions: Record<string, string[]> = {
    admin: ['read', 'write', 'configure', 'manage_users'],
    operator: ['read', 'write', 'configure'],
    viewer: ['read']
};

function checkPermission(
    requiredPermission: string,
    userRole: UserRole
): boolean {
    return userRole.permissions.includes(requiredPermission);
}
```

{{ ... }}
