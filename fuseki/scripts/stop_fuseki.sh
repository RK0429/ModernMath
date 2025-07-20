#!/bin/bash

# Stop Apache Jena Fuseki

echo "Stopping Apache Jena Fuseki..."

# Find and kill the Fuseki process
if pgrep -f "fuseki-server" > /dev/null; then
    pkill -f "fuseki-server"
    echo "Fuseki server stopped."
else
    echo "No Fuseki server process found."
fi