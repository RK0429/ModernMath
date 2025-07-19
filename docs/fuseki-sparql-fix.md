# Fuseki SPARQL Query Fix

## Issue

After loading data into Apache Jena Fuseki with TDB2, SPARQL queries were returning 0 results even though the data was successfully loaded (276 triples).

## Root Cause

Fuseki was loading the data into a special graph called `urn:x-arq:DefaultGraph` rather than the standard default graph. This is a known behavior when using TDB2 with certain configurations.

## Solution

Add `FROM <urn:x-arq:DefaultGraph>` to all SPARQL queries. This explicitly tells Fuseki to query the graph where the data is stored.

### Example Before (returns 0 results):
```sparql
PREFIX mymath: <https://mathwiki.org/ontology#>
SELECT ?s ?label
WHERE {
    ?s a mymath:Definition .
    ?s rdfs:label ?label .
}
```

### Example After (returns correct results):
```sparql
PREFIX mymath: <https://mathwiki.org/ontology#>
SELECT ?s ?label
FROM <urn:x-arq:DefaultGraph>
WHERE {
    ?s a mymath:Definition .
    ?s rdfs:label ?label .
}
```

## Files Updated

- `/fuseki/scripts/test_queries.py` - All test queries updated
- `/scripts/query_graph.py` - Query interface being updated
- `/api/app.py` - REST API queries need updating

## Alternative Solutions (not implemented)

1. Configure Fuseki to use unionDefaultGraph properly in the configuration
2. Load data directly into the default graph instead of a named graph
3. Use a different triple store that handles default graphs differently

## Verification

Run the test queries to verify:
```bash
poetry run python fuseki/scripts/test_queries.py
```

All queries should now return the expected results.