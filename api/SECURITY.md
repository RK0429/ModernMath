# API Security Documentation

## Overview

The Math Knowledge Graph API implements multiple layers of security to protect against common vulnerabilities and ensure safe operation.

## Security Features

### 1. Rate Limiting

- **Global limits**: 200 requests per day, 50 per hour per IP address
- **Endpoint-specific limits**:
  - Health check: 100/minute
  - Node queries: 30/minute
  - Search: 20/minute
  - Custom queries: 5/minute
  - Cache clear: 1/hour
  - Graph reload: 1/hour

### 2. CORS Configuration

- **Allowed origins**: 
  - `http://localhost:*` (development)
  - `https://rk0429.github.io` (production)
  - `https://*.github.io` (GitHub Pages)
- **Allowed methods**: GET, POST, OPTIONS
- **Allowed headers**: Content-Type, Authorization
- **Max age**: 3600 seconds

### 3. Input Validation

#### Node ID Validation
- Only alphanumeric characters, hyphens, and underscores allowed
- Pattern: `^[a-zA-Z0-9_-]+$`

#### Search Term Validation
- Maximum length: 100 characters
- Dangerous characters blocked: `<`, `>`, `"`, `'`, `\`, null bytes, newlines

#### SPARQL Query Validation
- Only SELECT queries allowed
- Dangerous keywords blocked: INSERT, DELETE, DROP, CREATE, etc.
- Complexity limits:
  - Maximum complexity score: 100
  - Maximum variables: 20
  - Maximum UNION clauses: 5
  - Maximum OPTIONAL clauses: 10
- Query timeout: 10 seconds

### 4. Authentication

JWT-based authentication for write operations:

```bash
# Login to get token
curl -X POST http://localhost:5001/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"username": "admin", "password": "your-password"}'

# Use token for protected endpoints
curl -X POST http://localhost:5001/api/admin/reload-graph \
  -H "Authorization: Bearer <your-token>"
```

### 5. Output Sanitization

All output is sanitized to prevent XSS attacks:
- HTML entities are escaped
- Special characters are encoded

### 6. Environment Variables

Set these environment variables for production:

```bash
# JWT secret key (required for production)
export JWT_SECRET_KEY="your-secure-random-key"

# Admin password for authentication
export ADMIN_PASSWORD="your-secure-password"

# Redis URL for distributed rate limiting (optional)
export REDIS_URL="redis://localhost:6379"

# Fuseki endpoint
export FUSEKI_ENDPOINT="http://localhost:3030/mathwiki/sparql"

# Flask environment
export FLASK_ENV="production"
```

## Query Complexity Scoring

The complexity score is calculated based on:

- Query length (1 point per 100 characters)
- Triple patterns (2 points each)
- OPTIONAL patterns (5 points each)
- UNION patterns (10 points each)
- FILTER expressions (3 points each)
- Property paths (15 points each)
- Subqueries (8 points each after the first)
- Aggregation functions (10 points each)

## Security Best Practices

1. **Always use HTTPS in production**
2. **Keep JWT secret key secure and rotate regularly**
3. **Monitor rate limit violations**
4. **Review SPARQL queries in logs for suspicious patterns**
5. **Keep dependencies updated**
6. **Use environment variables for sensitive configuration**
7. **Enable request logging for audit trails**

## Testing Security Features

### Test Rate Limiting
```python
# See api/test_rate_limit.py for comprehensive tests
```

### Test Input Validation
```python
# Invalid node ID
response = requests.get("http://localhost:5001/api/nodes/<script>alert('xss')</script>")
assert response.status_code == 400

# Invalid search term
response = requests.get("http://localhost:5001/api/search?q=" + "x" * 101)
assert response.status_code == 400
```

### Test Query Complexity
```python
# Complex query that should be rejected
complex_query = """
SELECT * WHERE {
  ?s ?p ?o .
  OPTIONAL { ?s ?p1 ?o1 }
  OPTIONAL { ?s ?p2 ?o2 }
  # ... repeat 11 times
}
"""
response = requests.post("http://localhost:5001/api/query", 
                        json={"query": complex_query})
assert response.status_code == 400
```

## Deployment Recommendations

1. **Use a reverse proxy** (nginx) with:
   - SSL/TLS termination
   - Additional rate limiting
   - Request size limits
   - Security headers

2. **Deploy with gunicorn** instead of Flask development server:
   ```bash
   gunicorn -w 4 -b 0.0.0.0:5001 api.app_secure:app
   ```

3. **Enable monitoring** for:
   - Failed authentication attempts
   - Rate limit violations
   - Query timeouts
   - Error rates

4. **Regular security audits**:
   - Review access logs
   - Update dependencies
   - Test security features
   - Review SPARQL query patterns