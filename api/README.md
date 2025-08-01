# Math Knowledge Graph REST API

A Flask-based REST API for querying the mathematical knowledge graph.

## API Documentation

### OpenAPI Specification

The API is fully documented using OpenAPI 3.0 specification:

- `openapi.yaml` - Complete OpenAPI 3.0 specification
- `swagger-ui.html` - Interactive API documentation

### Interactive Documentation

To view the interactive API documentation:

1. Open `swagger-ui.html` in a web browser while the API server is running
2. Or serve the API directory with a local HTTP server:

   ```bash
   cd api
   python -m http.server 8080
   # Then visit http://localhost:8080/swagger-ui.html
   ```

## Setup

### Prerequisites

1. Make sure you have completed the poetry installation:

   ```bash
   poetry install
   ```

2. Ensure Apache Jena Fuseki is running:

   ```bash
   cd fuseki
   ./scripts/start_fuseki.sh
   ```

3. Load the knowledge graph data into Fuseki:

   ```bash
   ./scripts/load_data.sh
   ```

## Running the API

1. Activate the poetry environment:

   ```bash
   poetry shell
   ```

2. Start the Flask development server:

   ```bash
   cd api
   python app.py
   ```

The API will be available at `http://localhost:5001`

## API Endpoints

### Health Check

- **GET** `/api/health`
- Returns the API status

### Get Node Details

- **GET** `/api/nodes/{node_id}`
- Example: `/api/nodes/def-group`
- Returns details about a specific mathematical concept

### Get Dependencies

- **GET** `/api/dependencies/{node_id}`
- Example: `/api/dependencies/thm-unique-identity`
- Returns all concepts that the specified node depends on

### Get Dependents

- **GET** `/api/dependents/{node_id}`
- Example: `/api/dependents/def-group`
- Returns all concepts that depend on the specified node

### Search Nodes

- **GET** `/api/search?q={search_term}`
- Example: `/api/search?q=group`
- Searches for nodes by label text using SPARQL queries

### Get All Nodes

- **GET** `/api/nodes`
- Returns all nodes in the knowledge graph

### Custom SPARQL Query

- **POST** `/api/query`
- Body: `{"query": "SELECT ... WHERE { ... }"}`
- Executes a custom SPARQL query (SELECT queries only)

### Cache Management

- **GET** `/api/cache/stats`
- Returns cache statistics (number of entries, status)
- **POST** `/api/cache/clear`
- Clears all cached responses

## Testing

Run the test suite to verify the API is working:

```bash
poetry run python api/test_api.py
```

## Example Usage

### Using curl

Get information about the group definition:

```bash
curl http://localhost:5001/api/nodes/def-group
```

Search for concepts containing "topology":

```bash
curl "http://localhost:5001/api/search?q=topology"
```

Get dependencies of a theorem:

```bash
curl http://localhost:5001/api/dependencies/thm-rank-nullity
```

### Using Python

```python
import requests

# Get node details
response = requests.get("http://localhost:5001/api/nodes/def-group")
data = response.json()
print(data)

# Search for concepts
response = requests.get("http://localhost:5001/api/search", params={"q": "vector"})
results = response.json()
for result in results["results"]:
    print(f"{result['label']} ({result['type']})")
```

### Custom SPARQL Query

```python
import requests

query = """
PREFIX mymath: <https://mathwiki.org/ontology#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

SELECT ?theorem ?label
WHERE {
    ?theorem a mymath:Theorem ;
            mymath:uses <https://mathwiki.org/resource/def-group> ;
            rdfs:label ?label .
}
"""

response = requests.post(
    "http://localhost:5001/api/query",
    json={"query": query}
)
results = response.json()
```

## CORS Support

The API includes CORS headers to allow cross-origin requests from web applications.

## Caching

The API implements an in-memory cache to improve performance:

- **Cache TTL (Time To Live)**:
  - Node details, dependencies, dependents: 10 minutes
  - Search results and suggestions: 5 minutes
  - All nodes listing: 15 minutes

- **Cache Management**:
  - Automatic cleanup of expired entries every 5 minutes
  - Manual cache clearing via `/api/cache/clear` endpoint
  - Cache statistics available at `/api/cache/stats`

- **Testing Cache**:

  ```bash
  poetry run python api/test_cache.py
  ```

## Rate Limiting

The API implements rate limiting to ensure fair usage and protect against abuse:

### Default Limits

- **Global limits**: 200 requests per day, 50 requests per hour (per IP address)

### Endpoint-Specific Limits (per minute)

- `/api/health`: 100 requests
- `/api/nodes/{node_id}`: 30 requests
- `/api/dependencies/{node_id}`: 30 requests
- `/api/dependents/{node_id}`: 30 requests
- `/api/search`: 20 requests
- `/api/nodes`: 10 requests
- `/api/query`: 5 requests (custom SPARQL queries)
- `/api/cache/stats`: 10 requests
- `/api/cache/clear`: 1 request per hour

### Rate Limit Headers

All responses include rate limit information in the headers:

- `X-RateLimit-Limit`: The rate limit for the endpoint
- `X-RateLimit-Remaining`: Number of requests remaining in the current window
- `X-RateLimit-Reset`: Unix timestamp when the rate limit window resets

### Rate Limit Exceeded

When the rate limit is exceeded, the API returns:

- **Status Code**: 429 Too Many Requests
- **Response Body**:

  ```json
  {
    "error": "Rate limit exceeded",
    "message": "Too many requests from this IP. Please try again later.",
    "retry_after": "60"
  }
  ```

- **Retry-After Header**: Seconds to wait before retrying

### Testing Rate Limits

```bash
# Test rate limiting functionality
poetry run python api/test_rate_limit.py
```

## Error Handling

The API returns appropriate HTTP status codes:

- 200: Success
- 400: Bad Request (missing parameters)
- 404: Resource not found
- 429: Too Many Requests (rate limit exceeded)
- 503: Service Unavailable (Fuseki not running)

## Production Deployment

For production deployment:

1. Use a production WSGI server like Gunicorn:

   ```bash
   gunicorn -w 4 -b 0.0.0.0:5001 api.app:app
   ```

2. Set up a reverse proxy with nginx

3. Configure environment variables for production settings

4. Enable proper logging and monitoring
