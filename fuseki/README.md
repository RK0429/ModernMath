# Apache Jena Fuseki Setup for Math Knowledge Graph

This directory contains scripts and configuration for running Apache Jena Fuseki as a SPARQL endpoint for the Math Knowledge Graph.

## Directory Structure

```
fuseki/
├── config/           # Fuseki configuration files
│   └── mathwiki.ttl  # Dataset configuration
├── data/             # TDB2 database files (created automatically)
├── scripts/          # Setup and utility scripts
│   ├── download_fuseki.sh  # Download Fuseki
│   ├── start_fuseki.sh     # Start Fuseki server
│   ├── load_data.sh        # Load knowledge graph data
│   └── test_queries.py     # Test SPARQL queries
└── README.md         # This file
```

## Quick Start

1. **Download Apache Jena Fuseki:**
   ```bash
   cd fuseki/scripts
   ./download_fuseki.sh
   ```

2. **Start Fuseki Server:**
   ```bash
   ./start_fuseki.sh
   ```
   The server will start at http://localhost:3030/

3. **Load Knowledge Graph Data:**
   First, ensure you've built the knowledge graph:
   ```bash
   cd ../..
   poetry run python scripts/build_graph.py
   ```
   
   Then load the data:
   ```bash
   cd fuseki/scripts
   ./load_data.sh
   ```

4. **Test SPARQL Queries:**
   ```bash
   poetry run python test_queries.py
   ```

## Accessing Fuseki

- **Web UI:** http://localhost:3030/
- **SPARQL Query Endpoint:** http://localhost:3030/mathwiki/sparql
- **SPARQL Update Endpoint:** http://localhost:3030/mathwiki/update
- **Graph Store Protocol:** http://localhost:3030/mathwiki/data

## Example SPARQL Queries

### Count all nodes
```sparql
PREFIX mymath: <https://mathwiki.org/ontology#>
SELECT (COUNT(DISTINCT ?node) as ?count)
WHERE {
    ?node a ?type .
}
```

### Find all definitions
```sparql
PREFIX mymath: <https://mathwiki.org/ontology#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

SELECT ?def ?label
WHERE {
    ?def a mymath:Definition .
    OPTIONAL { ?def rdfs:label ?label }
}
ORDER BY ?label
```

### Find dependencies of a theorem
```sparql
PREFIX mymath: <https://mathwiki.org/ontology#>
PREFIX base: <https://mathwiki.org/resource/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

SELECT ?dependency ?label
WHERE {
    base:thm-unique-identity mymath:uses ?dependency .
    OPTIONAL { ?dependency rdfs:label ?label }
}
```

## Troubleshooting

- **Port 3030 already in use:** Stop any existing Fuseki instances or change the port in the configuration
- **Data not loading:** Ensure Fuseki is running and the knowledge_graph.ttl file exists
- **Queries returning no results:** Check that data was loaded successfully using the Fuseki web UI

## Integration with CI/CD

The Fuseki setup can be integrated into the CI/CD pipeline for automated testing of the knowledge graph. See `.github/workflows/` for examples.