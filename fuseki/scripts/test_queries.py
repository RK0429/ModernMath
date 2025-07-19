#!/usr/bin/env python3
"""
Test SPARQL queries for the Math Knowledge Graph
"""

from SPARQLWrapper import SPARQLWrapper, JSON
import json

# SPARQL endpoint URL
ENDPOINT = "http://localhost:3030/mathwiki/sparql"

# Example queries
QUERIES = {
    "count_nodes": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        
        SELECT (COUNT(DISTINCT ?node) as ?count)
        WHERE {
            ?node a ?type .
            ?type rdfs:subClassOf* mymath:MathematicalObject .
        }
    """,
    
    "list_definitions": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        
        SELECT ?def ?label
        WHERE {
            ?def a mymath:Definition .
            OPTIONAL { ?def rdfs:label ?label }
        }
        ORDER BY ?label
    """,
    
    "find_dependencies": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX base: <https://mathwiki.org/resource/>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        
        SELECT ?dependency ?label
        WHERE {
            base:thm-unique-identity mymath:uses ?dependency .
            OPTIONAL { ?dependency rdfs:label ?label }
        }
    """,
    
    "find_theorems_using_definition": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX base: <https://mathwiki.org/resource/>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        
        SELECT ?theorem ?label
        WHERE {
            ?theorem mymath:uses base:def-group .
            ?theorem a mymath:Theorem .
            OPTIONAL { ?theorem rdfs:label ?label }
        }
    """,
    
    "get_domain_concepts": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        
        SELECT ?concept ?label ?domain
        WHERE {
            ?concept mymath:hasDomain ?domain .
            OPTIONAL { ?concept rdfs:label ?label }
            FILTER(?domain = "Algebra")
        }
        ORDER BY ?label
    """
}

def run_query(name, query):
    """Run a SPARQL query and print results"""
    print(f"\n{'='*60}")
    print(f"Query: {name}")
    print(f"{'='*60}")
    
    sparql = SPARQLWrapper(ENDPOINT)
    sparql.setQuery(query)
    sparql.setReturnFormat(JSON)
    
    try:
        results = sparql.query().convert()
        
        # Print results
        if "results" in results and "bindings" in results["results"]:
            bindings = results["results"]["bindings"]
            print(f"Found {len(bindings)} results:")
            
            for binding in bindings:
                row = []
                for var in results["head"]["vars"]:
                    if var in binding:
                        value = binding[var]["value"]
                        # Extract local name from URI if it's a URI
                        if binding[var]["type"] == "uri" and "#" in value:
                            value = value.split("#")[-1]
                        elif binding[var]["type"] == "uri" and "/" in value:
                            value = value.split("/")[-1]
                        row.append(f"{var}: {value}")
                print("  - " + ", ".join(row))
        else:
            print("No results found.")
            
    except Exception as e:
        print(f"Error executing query: {e}")
        print("Make sure Fuseki is running and data is loaded.")

def main():
    """Run all test queries"""
    print("Testing SPARQL queries on Math Knowledge Graph")
    print(f"Endpoint: {ENDPOINT}")
    
    # Check if SPARQLWrapper is installed
    try:
        import SPARQLWrapper
    except ImportError:
        print("\nError: SPARQLWrapper not installed.")
        print("Install it with: poetry add sparqlwrapper")
        return
    
    # Run each query
    for name, query in QUERIES.items():
        run_query(name, query)

if __name__ == "__main__":
    main()