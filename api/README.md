# Math Knowledge Graph REST API

A Flask-based REST API for querying the mathematical knowledge graph.

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

The API will be available at `http://localhost:5000`

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
- Searches for nodes by label text

### Get All Nodes
- **GET** `/api/nodes`
- Returns all nodes in the knowledge graph

### Custom SPARQL Query
- **POST** `/api/query`
- Body: `{"query": "SELECT ... WHERE { ... }"}`
- Executes a custom SPARQL query (SELECT queries only)

## Testing

Run the test suite to verify the API is working:

```bash
poetry run python api/test_api.py
```

## Example Usage

### Using curl

Get information about the group definition:
```bash
curl http://localhost:5000/api/nodes/def-group
```

Search for concepts containing "topology":
```bash
curl "http://localhost:5000/api/search?q=topology"
```

Get dependencies of a theorem:
```bash
curl http://localhost:5000/api/dependencies/thm-rank-nullity
```

### Using Python

```python
import requests

# Get node details
response = requests.get("http://localhost:5000/api/nodes/def-group")
data = response.json()
print(data)

# Search for concepts
response = requests.get("http://localhost:5000/api/search", params={"q": "vector"})
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
    "http://localhost:5000/api/query",
    json={"query": query}
)
results = response.json()
```

## CORS Support

The API includes CORS headers to allow cross-origin requests from web applications.

## Error Handling

The API returns appropriate HTTP status codes:
- 200: Success
- 400: Bad Request (missing parameters)
- 404: Resource not found
- 503: Service Unavailable (Fuseki not running)

## Production Deployment

For production deployment:

1. Use a production WSGI server like Gunicorn:
   ```bash
   gunicorn -w 4 -b 0.0.0.0:5000 api.app:app
   ```

2. Set up a reverse proxy with nginx

3. Configure environment variables for production settings

4. Enable proper logging and monitoring