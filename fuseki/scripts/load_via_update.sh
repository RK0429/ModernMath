#!/bin/bash

# Load knowledge graph data into Fuseki using SPARQL Update

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GRAPH_FILE="$SCRIPT_DIR/../../knowledge_graph.ttl"
UPDATE_ENDPOINT="http://localhost:3030/mathwiki/update"

# Check if the graph file exists
if [ ! -f "$GRAPH_FILE" ]; then
    echo "Error: knowledge_graph.ttl not found at $GRAPH_FILE"
    exit 1
fi

echo "Loading data via SPARQL Update endpoint..."

# First, clear existing data
echo "Clearing existing data..."
curl -X POST \
    -H "Content-Type: application/sparql-update" \
    --data "CLEAR DEFAULT" \
    "$UPDATE_ENDPOINT"

# Convert file content to SPARQL INSERT DATA statement
echo "Loading new data..."
(
    echo "INSERT DATA {"
    cat "$GRAPH_FILE"
    echo "}"
) | curl -X POST \
    -H "Content-Type: application/sparql-update" \
    --data-binary @- \
    "$UPDATE_ENDPOINT"

echo ""
echo "Data loading completed. Testing with a simple query..."

# Test query
curl -X POST \
    -H "Content-Type: application/sparql-query" \
    -H "Accept: application/json" \
    --data "SELECT (COUNT(*) as ?count) WHERE { ?s ?p ?o }" \
    "http://localhost:3030/mathwiki/sparql" | python3 -m json.tool
