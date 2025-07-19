#!/bin/bash

# Download and setup Apache Jena Fuseki script
# This script downloads the latest stable version of Apache Jena Fuseki

FUSEKI_VERSION="4.10.0"
FUSEKI_DIR="../fuseki-server"

echo "Downloading Apache Jena Fuseki ${FUSEKI_VERSION}..."

# Create directory if it doesn't exist
mkdir -p "$FUSEKI_DIR"

# Download Fuseki
cd "$FUSEKI_DIR"
curl -O "https://archive.apache.org/dist/jena/binaries/apache-jena-fuseki-${FUSEKI_VERSION}.tar.gz"

# Extract
echo "Extracting Fuseki..."
tar -xzf "apache-jena-fuseki-${FUSEKI_VERSION}.tar.gz"

# Create symlink for easier access
ln -sf "apache-jena-fuseki-${FUSEKI_VERSION}" current

echo "Fuseki downloaded and extracted successfully!"
echo "To start Fuseki, run: ./current/fuseki-server"