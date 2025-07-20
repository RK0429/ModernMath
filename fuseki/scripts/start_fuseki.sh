#!/bin/bash

# Start Apache Jena Fuseki with our Math Wiki configuration

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FUSEKI_DIR="$SCRIPT_DIR/../fuseki-server/current"
CONFIG_FILE="$SCRIPT_DIR/../config/mathwiki.ttl"

# Add Homebrew OpenJDK to PATH if not already present
if ! command -v java &> /dev/null; then
    export PATH="/opt/homebrew/opt/openjdk/bin:$PATH"
fi

# Check if Java is available
if ! java --version &> /dev/null; then
    echo "Error: Java is not available. Please install Java 11 or later."
    echo "On macOS with Homebrew: brew install openjdk"
    echo "Then add to PATH: export PATH=\"/opt/homebrew/opt/openjdk/bin:\$PATH\""
    exit 1
fi

# Check if Fuseki is installed
if [ ! -d "$FUSEKI_DIR" ]; then
    echo "Fuseki not found. Please run download_fuseki.sh first."
    exit 1
fi

# Create data directory if it doesn't exist
mkdir -p "$SCRIPT_DIR/../data"

# Start Fuseki with our configuration
echo "Starting Apache Jena Fuseki..."
echo "Configuration: $CONFIG_FILE"
echo "Access the UI at: http://localhost:3030/"
echo "SPARQL endpoint: http://localhost:3030/mathwiki/sparql"

cd "$FUSEKI_DIR"
./fuseki-server --config="$CONFIG_FILE"
