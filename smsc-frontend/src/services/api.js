const API_BASE_URL = 'http://localhost:8080/api';

export const submitMessage = async (message) => {
  const response = await fetch(`${API_BASE_URL}/messages`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify(message),
  });
  
  if (!response.ok) {
    throw new Error('Failed to submit message');
  }
  
  return response.json();
};

export const queryMessage = async (messageId) => {
  const response = await fetch(`${API_BASE_URL}/messages/${messageId}`);
  
  if (!response.ok) {
    throw new Error('Failed to query message');
  }
  
  return response.json();
};

export const cancelMessage = async (messageId) => {
  const response = await fetch(`${API_BASE_URL}/messages/${messageId}`, {
    method: 'DELETE',
  });
  
  if (!response.ok) {
    throw new Error('Failed to cancel message');
  }
  
  return response.json();
};

export const getMetrics = async () => {
  const response = await fetch(`${API_BASE_URL}/metrics`);
  
  if (!response.ok) {
    throw new Error('Failed to get metrics');
  }
  
  return response.json();
};
