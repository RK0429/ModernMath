#!/bin/bash

# Start Apache Jena Fuseki with in-memory configuration

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FUSEKI_DIR="$SCRIPT_DIR/../fuseki-server/current"
CONFIG_FILE="$SCRIPT_DIR/../config/mathwiki-memory.ttl"
LOG_FILE="$SCRIPT_DIR/../fuseki-memory.log"

# Add Homebrew OpenJDK to PATH
export PATH="/opt/homebrew/opt/openjdk/bin:$PATH"

echo "Starting Apache Jena Fuseki with in-memory dataset..."
echo "Configuration: $CONFIG_FILE"
echo "Log file: $LOG_FILE"

# Start Fuseki in the background
cd "$FUSEKI_DIR"
nohup ./fuseki-server --config="$CONFIG_FILE" > "$LOG_FILE" 2>&1 &

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
