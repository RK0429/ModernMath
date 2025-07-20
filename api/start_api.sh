#!/bin/bash
# Start the Math Knowledge Graph REST API

echo "Starting Math Knowledge Graph REST API..."
echo "========================================"

# Check if we're in the right directory
if [ ! -f "app.py" ]; then
    echo "Error: app.py not found. Please run this script from the api/ directory."
    exit 1
fi

# Check if Fuseki is running
if ! curl -s http://localhost:3030 > /dev/null; then
    echo "Warning: Apache Jena Fuseki doesn't appear to be running on http://localhost:3030"
    echo "The API will start but may not function properly without Fuseki."
    echo "To start Fuseki, run: ./fuseki/scripts/start_fuseki.sh"
    echo ""
fi

# Activate poetry environment and run the app
echo "Starting Flask server on http://localhost:5000"
echo ""
cd ..
poetry run python api/app.py
