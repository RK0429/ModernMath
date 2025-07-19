#!/bin/bash

# Math Knowledge Graph Wiki - Status Check
# This script checks the status of all services and the project

echo "📊 Math Knowledge Graph Wiki Status Check"
echo "========================================"
echo ""

# Check Fuseki status
echo "🔍 Checking Apache Jena Fuseki..."
if lsof -i :3030 | grep -q LISTEN; then
    echo "✅ Fuseki is running on port 3030"
    # Try to query the endpoint
    if curl -s -f "http://localhost:3030/mathwiki/query" -d "query=SELECT ?s WHERE { ?s ?p ?o } LIMIT 1" > /dev/null 2>&1; then
        echo "✅ SPARQL endpoint is responding"
    else
        echo "⚠️  SPARQL endpoint is not responding properly"
    fi
else
    echo "❌ Fuseki is not running"
fi

echo ""

# Check REST API status
echo "🔍 Checking REST API..."
if lsof -i :5001 | grep -q LISTEN; then
    echo "✅ REST API is running on port 5001"
    # Try to hit the health endpoint
    HEALTH=$(curl -s http://localhost:5001/api/health 2>/dev/null | grep -o '"status": *"healthy"' || echo "")
    if [ -n "$HEALTH" ]; then
        echo "✅ API health check passed"
    else
        echo "⚠️  API health check failed"
    fi
else
    echo "❌ REST API is not running"
fi

echo ""

# Check knowledge graph
echo "🔍 Checking Knowledge Graph..."
if [ -f "knowledge_graph.ttl" ]; then
    TRIPLE_COUNT=$(grep -c "^\s*<" knowledge_graph.ttl || echo "0")
    echo "✅ Knowledge graph exists with approximately $TRIPLE_COUNT triples"
else
    echo "❌ Knowledge graph file not found"
fi

echo ""

# Check search index
echo "🔍 Checking Search Index..."
if [ -d "search_index" ] && [ -f "search_index/_MAIN_1.toc" ]; then
    echo "✅ Search index exists"
else
    echo "❌ Search index not found"
fi

echo ""

# Check site build
echo "🔍 Checking Site Build..."
if [ -d "_site" ] && [ -f "_site/index.html" ]; then
    FILE_COUNT=$(find _site -name "*.html" | wc -l)
    echo "✅ Site is built with $FILE_COUNT HTML files"
else
    echo "❌ Site has not been built"
fi

echo ""

# Check GitHub Pages
echo "🔍 Checking GitHub Pages deployment..."
HTTP_STATUS=$(curl -s -o /dev/null -w "%{http_code}" https://RK0429.github.io/ModernMath/ 2>/dev/null)
if [ "$HTTP_STATUS" = "200" ]; then
    echo "✅ GitHub Pages site is live at https://RK0429.github.io/ModernMath/"
elif [ "$HTTP_STATUS" = "404" ]; then
    echo "⚠️  GitHub Pages returns 404 - manual enablement required in repository settings"
else
    echo "❌ Unable to check GitHub Pages status (HTTP $HTTP_STATUS)"
fi

echo ""
echo "========================================"
echo ""

# Summary
echo "📝 Summary:"
if lsof -i :3030 | grep -q LISTEN && lsof -i :5001 | grep -q LISTEN; then
    echo "✅ All local services are running"
else
    echo "⚠️  Some services are not running. Run ./start_all_services.sh to start them."
fi

if [ "$HTTP_STATUS" != "200" ]; then
    echo ""
    echo "⚠️  GitHub Pages needs manual enablement:"
    echo "   1. Go to https://github.com/RK0429/ModernMath/settings/pages"
    echo "   2. Under 'Source', select 'Deploy from a branch'"
    echo "   3. Select 'gh-pages' branch and '/ (root)' folder"
    echo "   4. Click 'Save'"
fi