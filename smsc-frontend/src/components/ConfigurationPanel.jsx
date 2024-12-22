import React, { useState, useEffect } from 'react';
import {
    Box,
    Card,
    CardContent,
    TextField,
    Button,
    Typography,
    Snackbar,
    Alert,
    Grid
} from '@mui/material';
import { configService } from '../services/configService';

export const ConfigurationPanel = () => {
    const [config, setConfig] = useState({
        smsc_host: '',
        smsc_port: '',
        system_id: '',
        password: '',
        system_type: '',
        interface_version: '',
    });

    const [notification, setNotification] = useState({
        open: false,
        message: '',
        severity: 'success'
    });

    const [loading, setLoading] = useState(false);

    useEffect(() => {
        loadConfiguration();
    }, []);

    const loadConfiguration = async () => {
        try {
            setLoading(true);
            const loadedConfig = await configService.loadConfig();
            setConfig(loadedConfig);
        } catch (error) {
            showNotification('Failed to load configuration: ' + error.message, 'error');
        } finally {
            setLoading(false);
        }
    };

    const handleInputChange = (event) => {
        const { name, value } = event.target;
        setConfig(prevConfig => ({
            ...prevConfig,
            [name]: value
        }));
    };

    const handleSave = async () => {
        try {
            setLoading(true);
            await configService.saveConfig(config);
            showNotification('Configuration saved successfully', 'success');
        } catch (error) {
            showNotification('Failed to save configuration: ' + error.message, 'error');
        } finally {
            setLoading(false);
        }
    };

    const showNotification = (message, severity) => {
        setNotification({
            open: true,
            message,
            severity
        });
    };

    const handleCloseNotification = () => {
        setNotification(prev => ({
            ...prev,
            open: false
        }));
    };

    return (
        <Box sx={{ p: 3 }}>
            <Card>
                <CardContent>
                    <Typography variant="h5" gutterBottom>
                        SMSC Configuration
                    </Typography>
                    <Grid container spacing={2}>
                        <Grid item xs={12} md={6}>
                            <TextField
                                fullWidth
                                label="SMSC Host"
                                name="smsc_host"
                                value={config.smsc_host}
                                onChange={handleInputChange}
                                margin="normal"
                                disabled={loading}
                            />
                        </Grid>
                        <Grid item xs={12} md={6}>
                            <TextField
                                fullWidth
                                label="SMSC Port"
                                name="smsc_port"
                                value={config.smsc_port}
                                onChange={handleInputChange}
                                margin="normal"
                                type="number"
                                disabled={loading}
                            />
                        </Grid>
                        <Grid item xs={12} md={6}>
                            <TextField
                                fullWidth
                                label="System ID"
                                name="system_id"
                                value={config.system_id}
                                onChange={handleInputChange}
                                margin="normal"
                                disabled={loading}
                            />
                        </Grid>
                        <Grid item xs={12} md={6}>
                            <TextField
                                fullWidth
                                label="Password"
                                name="password"
                                value={config.password}
                                onChange={handleInputChange}
                                margin="normal"
                                type="password"
                                disabled={loading}
                            />
                        </Grid>
                        <Grid item xs={12} md={6}>
                            <TextField
                                fullWidth
                                label="System Type"
                                name="system_type"
                                value={config.system_type}
                                onChange={handleInputChange}
                                margin="normal"
                                disabled={loading}
                            />
                        </Grid>
                        <Grid item xs={12} md={6}>
                            <TextField
                                fullWidth
                                label="Interface Version"
                                name="interface_version"
                                value={config.interface_version}
                                onChange={handleInputChange}
                                margin="normal"
                                type="number"
                                disabled={loading}
                            />
                        </Grid>
                    </Grid>
                    <Box sx={{ mt: 3, display: 'flex', justifyContent: 'flex-end' }}>
                        <Button
                            variant="contained"
                            onClick={handleSave}
                            disabled={loading}
                        >
                            {loading ? 'Saving...' : 'Save Configuration'}
                        </Button>
                    </Box>
                </CardContent>
            </Card>
            <Snackbar
                open={notification.open}
                autoHideDuration={6000}
                onClose={handleCloseNotification}
                anchorOrigin={{ vertical: 'bottom', horizontal: 'right' }}
            >
                <Alert
                    onClose={handleCloseNotification}
                    severity={notification.severity}
                    sx={{ width: '100%' }}
                >
                    {notification.message}
                </Alert>
            </Snackbar>
        </Box>
    );
};
