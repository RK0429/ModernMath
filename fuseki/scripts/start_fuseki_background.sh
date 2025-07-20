#!/bin/bash

# Start Apache Jena Fuseki in the background

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOG_FILE="$SCRIPT_DIR/../fuseki.log"

# Add Homebrew OpenJDK to PATH
export PATH="/opt/homebrew/opt/openjdk/bin:$PATH"

# Check if Fuseki is already running
if lsof -i :3030 > /dev/null 2>&1; then
    echo "Fuseki appears to be already running on port 3030."
    exit 1
fi

echo "Starting Apache Jena Fuseki in the background..."
echo "Log file: $LOG_FILE"

# Start Fuseki in the background
nohup "$SCRIPT_DIR/start_fuseki.sh" > "$LOG_FILE" 2>&1 &

# Wait a moment for the server to start
sleep 3

# Check if the server started successfully
if lsof -i :3030 > /dev/null 2>&1; then
    echo "Fuseki server started successfully!"
    echo "Access the UI at: http://localhost:3030/"
    echo "SPARQL endpoint: http://localhost:3030/mathwiki/sparql"
    echo "PID: $(pgrep -f fuseki-server)"
else
    echo "Failed to start Fuseki server. Check the log file: $LOG_FILE"
    exit 1
fi