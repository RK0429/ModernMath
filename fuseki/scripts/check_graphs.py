#!/usr/bin/env python3
"""Check which graphs contain data in Fuseki"""

from SPARQLWrapper import SPARQLWrapper, JSON

ENDPOINT = "http://localhost:3030/mathwiki/sparql"

# Query to find all graphs
queries = [
    ("List all graphs", """
        SELECT DISTINCT ?g 
        WHERE {
            GRAPH ?g { ?s ?p ?o }
        }
    """),
    
    ("Count triples in each graph", """
        SELECT ?g (COUNT(*) as ?count)
        WHERE {
            GRAPH ?g { ?s ?p ?o }
        }
        GROUP BY ?g
    """),
    
    ("Count triples in default graph", """
        SELECT (COUNT(*) as ?count)
        WHERE { 
            ?s ?p ?o 
            FILTER NOT EXISTS { GRAPH ?g { ?s ?p ?o } }
        }
    """),
    
    ("Count ALL triples (including named graphs)", """
        SELECT (COUNT(*) as ?count)
        WHERE {
            { ?s ?p ?o }
            UNION
            { GRAPH ?g { ?s ?p ?o } }
        }
    """),
]

def run_query(name, query):
    print(f"\n{name}:")
    print("-" * 40)
    
    sparql = SPARQLWrapper(ENDPOINT)
    sparql.setQuery(query)
    sparql.setReturnFormat(JSON)
    
    try:
        results = sparql.query().convert()
        
        if "results" in results and "bindings" in results["results"]:
            bindings = results["results"]["bindings"]
            if bindings:
                for binding in bindings:
                    row = []
                    for var in results["head"]["vars"]:
                        if var in binding:
                            value = binding[var]["value"]
                            row.append(f"{var}: {value}")
                    print("  " + " | ".join(row))
            else:
                print("  No results")
        else:
            print("  No results")
            
    except Exception as e:
        print(f"  Error: {e}")

def main():
    print("Checking graphs in Fuseki")
    print(f"Endpoint: {ENDPOINT}")
    
    for name, query in queries:
        run_query(name, query)

if __name__ == "__main__":
    main()