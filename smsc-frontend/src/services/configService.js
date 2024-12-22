import { apiService } from './apiService';

const API_BASE_URL = 'http://localhost:8080/api';

export const configService = {
    async loadConfig() {
        try {
            const response = await apiService.get('/config');
            return response.config;
        } catch (error) {
            console.error('Error loading configuration:', error);
            throw error;
        }
    },

    async saveConfig(config) {
        try {
            await apiService.post('/config', config);
            return true;
        } catch (error) {
            console.error('Error saving configuration:', error);
            throw error;
        }
    }
};
