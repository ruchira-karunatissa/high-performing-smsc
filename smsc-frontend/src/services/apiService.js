const API_BASE_URL = 'http://localhost:8080/api';

class ApiService {
    async get(endpoint) {
        const response = await fetch(`${API_BASE_URL}${endpoint}`);
        const data = await response.json();
        if (data.status === 'error') {
            throw new Error(data.reason || 'API request failed');
        }
        return data;
    }

    async post(endpoint, body) {
        const response = await fetch(`${API_BASE_URL}${endpoint}`, {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json',
            },
            body: JSON.stringify(body),
        });
        const data = await response.json();
        if (data.status === 'error') {
            throw new Error(data.reason || 'API request failed');
        }
        return data;
    }

    async delete(endpoint) {
        const response = await fetch(`${API_BASE_URL}${endpoint}`, {
            method: 'DELETE',
        });
        const data = await response.json();
        if (data.status === 'error') {
            throw new Error(data.reason || 'API request failed');
        }
        return data;
    }
}

export const apiService = new ApiService();
