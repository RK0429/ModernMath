#!/bin/bash

# Load knowledge graph data into Fuseki

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GRAPH_FILE="$SCRIPT_DIR/../../output/knowledge_graph.ttl"
ENDPOINT="http://localhost:3030/mathwiki/data"

# Check if the graph file exists
if [ ! -f "$GRAPH_FILE" ]; then
    echo "Error: knowledge_graph.ttl not found at $GRAPH_FILE"
    echo "Please run the build_graph.py script first."
    exit 1
fi

# Check if Fuseki is running
if ! curl -s -o /dev/null -w "%{http_code}" http://localhost:3030/ | grep -q "200"; then
    echo "Error: Fuseki doesn't appear to be running."
    echo "Please start Fuseki with start_fuseki.sh first."
    exit 1
fi

echo "Loading knowledge graph data into Fuseki..."
echo "File: $GRAPH_FILE"
echo "Endpoint: $ENDPOINT"

# Load the data using curl
curl -X POST \
    -H "Content-Type: text/turtle" \
    --data-binary "@$GRAPH_FILE" \
    "$ENDPOINT"

if [ $? -eq 0 ]; then
    echo "Data loaded successfully!"
else
    echo "Error loading data."
    exit 1
fi