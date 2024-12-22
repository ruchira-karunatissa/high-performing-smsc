import React, { useState, useEffect } from 'react';
import {
  Container,
  Grid,
  Paper,
  Typography,
  Table,
  TableBody,
  TableCell,
  TableContainer,
  TableHead,
  TableRow,
  Box,
  CircularProgress,
} from '@mui/material';
import { LineChart, Line, XAxis, YAxis, CartesianGrid, Tooltip, Legend } from 'recharts';

const Dashboard = () => {
  const [metrics, setMetrics] = useState(null);
  const [historicalData, setHistoricalData] = useState([]);
  const [ws, setWs] = useState(null);

  useEffect(() => {
    // Initialize WebSocket connection
    const websocket = new WebSocket('ws://localhost:8080/ws');
    
    websocket.onopen = () => {
      console.log('Connected to SMSC WebSocket');
    };

    websocket.onmessage = (event) => {
      const newMetrics = JSON.parse(event.data);
      setMetrics(newMetrics);
      
      // Add to historical data
      setHistoricalData(prev => {
        const newData = [...prev, { ...newMetrics, timestamp: new Date() }];
        // Keep last 60 data points (1 minute of data)
        return newData.slice(-60);
      });
    };

    websocket.onerror = (error) => {
      console.error('WebSocket error:', error);
    };

    setWs(websocket);

    // Cleanup on unmount
    return () => {
      if (websocket) {
        websocket.close();
      }
    };
  }, []);

  if (!metrics) {
    return (
      <Box display="flex" justifyContent="center" alignItems="center" minHeight="100vh">
        <CircularProgress />
      </Box>
    );
  }

  return (
    <Container maxWidth="lg" sx={{ mt: 4, mb: 4 }}>
      <Grid container spacing={3}>
        {/* Metrics Summary */}
        <Grid item xs={12} md={4}>
          <Paper sx={{ p: 2, display: 'flex', flexDirection: 'column' }}>
            <Typography component="h2" variant="h6" color="primary" gutterBottom>
              System Status
            </Typography>
            <Typography component="p" variant="h4">
              {metrics.status}
            </Typography>
          </Paper>
        </Grid>
        <Grid item xs={12} md={4}>
          <Paper sx={{ p: 2, display: 'flex', flexDirection: 'column' }}>
            <Typography component="h2" variant="h6" color="primary" gutterBottom>
              Active Connections
            </Typography>
            <Typography component="p" variant="h4">
              {metrics.connections}
            </Typography>
          </Paper>
        </Grid>
        <Grid item xs={12} md={4}>
          <Paper sx={{ p: 2, display: 'flex', flexDirection: 'column' }}>
            <Typography component="h2" variant="h6" color="primary" gutterBottom>
              Messages/sec
            </Typography>
            <Typography component="p" variant="h4">
              {metrics.messages_per_second}
            </Typography>
          </Paper>
        </Grid>

        {/* Message Rate Chart */}
        <Grid item xs={12}>
          <Paper sx={{ p: 2 }}>
            <Typography component="h2" variant="h6" color="primary" gutterBottom>
              Message Rate Over Time
            </Typography>
            <LineChart
              width={1100}
              height={300}
              data={historicalData}
              margin={{ top: 5, right: 30, left: 20, bottom: 5 }}
            >
              <CartesianGrid strokeDasharray="3 3" />
              <XAxis
                dataKey="timestamp"
                tickFormatter={(timestamp) => new Date(timestamp).toLocaleTimeString()}
              />
              <YAxis />
              <Tooltip
                labelFormatter={(timestamp) => new Date(timestamp).toLocaleTimeString()}
              />
              <Legend />
              <Line
                type="monotone"
                dataKey="messages_per_second"
                stroke="#8884d8"
                name="Messages/sec"
              />
            </LineChart>
          </Paper>
        </Grid>

        {/* Recent Messages Table */}
        <Grid item xs={12}>
          <Paper sx={{ p: 2 }}>
            <Typography component="h2" variant="h6" color="primary" gutterBottom>
              Recent Messages
            </Typography>
            <TableContainer>
              <Table>
                <TableHead>
                  <TableRow>
                    <TableCell>Message ID</TableCell>
                    <TableCell>Status</TableCell>
                    <TableCell>Priority</TableCell>
                    <TableCell>Timestamp</TableCell>
                  </TableRow>
                </TableHead>
                <TableBody>
                  {metrics.recent_messages?.map((message) => (
                    <TableRow key={message.id}>
                      <TableCell>{message.id}</TableCell>
                      <TableCell>{message.status}</TableCell>
                      <TableCell>{message.priority}</TableCell>
                      <TableCell>
                        {new Date(message.timestamp).toLocaleString()}
                      </TableCell>
                    </TableRow>
                  ))}
                </TableBody>
              </Table>
            </TableContainer>
          </Paper>
        </Grid>
      </Grid>
    </Container>
  );
};

export default Dashboard;
