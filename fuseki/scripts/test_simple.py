#!/usr/bin/env python3
"""Simple test to verify Fuseki data access"""

from SPARQLWrapper import SPARQLWrapper, JSON

ENDPOINT = "http://localhost:3030/mathwiki/sparql"

# Try different query approaches
queries = [
    # 1. Simple count with FROM
    """
    SELECT (COUNT(*) as ?count)
    FROM <urn:x-arq:DefaultGraph>
    WHERE { ?s ?p ?o }
    """,
    
    # 2. Count with explicit default graph
    """
    SELECT (COUNT(*) as ?count)
    WHERE { 
        GRAPH <urn:x-arq:DefaultGraph> { ?s ?p ?o }
    }
    """,
    
    # 3. Union of default and named graphs
    """
    SELECT (COUNT(*) as ?count)
    WHERE { 
        { ?s ?p ?o }
        UNION
        { GRAPH ?g { ?s ?p ?o } }
    }
    """,
    
    # 4. Direct query without graph specification
    """
    PREFIX mymath: <https://mathwiki.org/ontology#>
    SELECT ?s ?label
    WHERE { 
        ?s a mymath:Definition .
        ?s <http://www.w3.org/2000/01/rdf-schema#label> ?label .
    }
    LIMIT 5
    """,
]

def test_query(query, desc):
    print(f"\nTesting: {desc}")
    print("-" * 50)
    
    sparql = SPARQLWrapper(ENDPOINT)
    sparql.setQuery(query)
    sparql.setReturnFormat(JSON)
    
    try:
        results = sparql.query().convert()
        
        if "results" in results and "bindings" in results["results"]:
            bindings = results["results"]["bindings"]
            print(f"Results: {len(bindings)} rows")
            
            for i, binding in enumerate(bindings[:3]):  # Show first 3
                row = []
                for var in results["head"]["vars"]:
                    if var in binding:
                        value = binding[var]["value"]
                        row.append(f"{var}={value}")
                print(f"  [{i+1}] " + ", ".join(row))
                
            if len(bindings) > 3:
                print(f"  ... and {len(bindings) - 3} more")
    except Exception as e:
        print(f"Error: {e}")

def main():
    print("Testing Fuseki SPARQL endpoint")
    print(f"Endpoint: {ENDPOINT}")
    
    descriptions = [
        "Count with FROM DefaultGraph",
        "Count with GRAPH DefaultGraph", 
        "Count with UNION",
        "Direct query for Definitions"
    ]
    
    for query, desc in zip(queries, descriptions):
        test_query(query, desc)

if __name__ == "__main__":
    main()