#!/bin/bash

# Test different methods of loading data into Fuseki

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GRAPH_FILE="$SCRIPT_DIR/../../knowledge_graph.ttl"

echo "Testing data load methods for Fuseki..."
echo "Graph file: $GRAPH_FILE"

# Method 1: Using GSP (Graph Store Protocol)
echo ""
echo "Method 1: Using Graph Store Protocol (GSP)..."
curl -X PUT \
    -H "Content-Type: text/turtle" \
    --data-binary "@$GRAPH_FILE" \
    "http://localhost:3030/mathwiki/data?default"

echo ""
echo "Testing if data was loaded..."
curl -X POST \
    -H "Content-Type: application/sparql-query" \
    -H "Accept: application/json" \
    --data "SELECT (COUNT(*) as ?count) WHERE { ?s ?p ?o }" \
    "http://localhost:3030/mathwiki/sparql" | python3 -m json.tool

echo ""
echo "Checking first few triples..."
curl -X POST \
    -H "Content-Type: application/sparql-query" \
    -H "Accept: application/json" \
    --data "SELECT ?s ?p ?o WHERE { ?s ?p ?o } LIMIT 5" \
    "http://localhost:3030/mathwiki/sparql" | python3 -m json.tool
