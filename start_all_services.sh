#!/bin/bash

# Math Knowledge Graph Wiki - Start All Services
# This script starts all required services for the wiki

echo "🚀 Starting Math Knowledge Graph Wiki Services..."

# Check if Fuseki is already running
if lsof -i :3030 | grep -q LISTEN; then
    echo "✓ Fuseki is already running on port 3030"
else
    echo "Starting Apache Jena Fuseki..."
    cd fuseki
    ./scripts/start_fuseki.sh &
    cd ..
    sleep 5
    echo "✓ Fuseki started on port 3030"
fi

# Check if REST API is already running
if lsof -i :5001 | grep -q LISTEN; then
    echo "✓ REST API is already running on port 5001"
else
    echo "Starting REST API..."
    cd api
    ./start_api.sh &
    cd ..
    sleep 3
    echo "✓ REST API started on port 5001"
fi

echo ""
echo "🎉 All services are running!"
echo ""
echo "📍 Service URLs:"
echo "   - Fuseki SPARQL endpoint: http://localhost:3030/mathwiki"
echo "   - REST API: http://localhost:5001"
echo "   - API Documentation: http://localhost:5001/api/docs"
echo ""
echo "📝 To view the site locally:"
echo "   1. Make sure the site is built: quarto render"
echo "   2. Start a local server: python -m http.server 8000 --directory _site"
echo "   3. Open: http://localhost:8000"
echo ""
echo "🛑 To stop services:"
echo "   - Fuseki: kill $(lsof -ti:3030)"
echo "   - REST API: kill $(lsof -ti:5001)"