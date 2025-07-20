# Fuseki SPARQL Query Fix

## Issue History

### Original Issue (TDB2 Default Graph)
After loading data into Apache Jena Fuseki with TDB2, SPARQL queries were returning 0 results even though the data was successfully loaded (276 triples). Fuseki was loading the data into a special graph called `urn:x-arq:DefaultGraph` rather than the standard default graph.

### Current Issue (Java PATH and TDB2 Configuration)
1. **Java Installation**: OpenJDK was installed via Homebrew but not in the system PATH, causing Fuseki startup failures
2. **TDB2 Configuration**: The persistent TDB2 storage wasn't working properly with data loading (queries returning 0 results)

## Current Solution

### 1. Fixed Java PATH Issue

Updated the Fuseki startup scripts to include Homebrew's OpenJDK in the PATH:

```bash
# Add Homebrew OpenJDK to PATH if not already present
if ! command -v java &> /dev/null; then
    export PATH="/opt/homebrew/opt/openjdk/bin:$PATH"
fi
```

### 2. Created In-Memory Configuration

Created a simpler in-memory configuration (`fuseki/config/mathwiki-memory.ttl`) that works reliably:

```turtle
@prefix :      <http://base/#> .
@prefix fuseki: <http://jena.apache.org/fuseki#> .
@prefix rdf:   <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs:  <http://www.w3.org/2000/01/rdf-schema#> .
@prefix ja:    <http://jena.hpl.hp.com/2005/11/Assembler#> .

# Service configuration for the Math Knowledge Graph (in-memory)
<#service> rdf:type fuseki:Service ;
    fuseki:name                       "mathwiki" ;
    fuseki:serviceQuery               "sparql" ;
    fuseki:serviceQuery               "query" ;
    fuseki:serviceUpdate              "update" ;
    fuseki:serviceUpload              "upload" ;
    fuseki:serviceReadWriteGraphStore "data" ;
    fuseki:serviceReadGraphStore      "get" ;
    fuseki:dataset                    <#dataset> .

# In-memory dataset configuration
<#dataset> rdf:type ja:MemoryDataset .
```

### 3. Created Helper Scripts

- `start_fuseki_memory.sh`: Starts Fuseki with in-memory configuration
- `start_fuseki_background.sh`: Starts Fuseki in background with proper Java PATH
- `stop_fuseki.sh`: Stops the Fuseki server

## Usage

1. Start Fuseki with in-memory configuration:
   ```bash
   ./fuseki/scripts/start_fuseki_memory.sh
   ```

2. Load the knowledge graph data:
   ```bash
   ./fuseki/scripts/load_data.sh
   ```

3. Test the SPARQL endpoint:
   ```bash
   curl -X POST http://localhost:3030/mathwiki/sparql \
     -H "Accept: application/sparql-results+json" \
     -d "query=SELECT (COUNT(*) as ?count) WHERE { ?s ?p ?o }"
   ```

## Current Status (2025-07-20)

- ✅ SPARQL endpoint working at `http://localhost:3030/mathwiki/sparql`
- ✅ 400 triples loaded successfully
- ✅ Queries returning correct results without needing `FROM <urn:x-arq:DefaultGraph>`
- ✅ Web UI accessible at `http://localhost:3030/`

## Note on Persistence

The current solution uses in-memory storage, which means data needs to be reloaded after each server restart. For production use, the TDB2 configuration should be debugged further or consider using a different persistent storage solution.

## Verification

Run the test queries to verify:
```bash
poetry run python fuseki/scripts/test_queries.py
```

All queries should now return the expected results.
