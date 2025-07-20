#!/usr/bin/env python3
"""Debug SPARQL queries to check data loading"""

from SPARQLWrapper import SPARQLWrapper, JSON

ENDPOINT = "http://localhost:3030/mathwiki/sparql"

# Start with the simplest possible queries
QUERIES = [
    (
        "Count all triples",
        """
        SELECT (COUNT(*) as ?count)
        WHERE { ?s ?p ?o }
    """,
    ),
    (
        "List first 10 triples",
        """
        SELECT ?s ?p ?o
        WHERE { ?s ?p ?o }
        LIMIT 10
    """,
    ),
    (
        "Count nodes with type",
        """
        SELECT (COUNT(DISTINCT ?s) as ?count)
        WHERE { ?s a ?type }
    """,
    ),
    (
        "List types used",
        """
        SELECT DISTINCT ?type
        WHERE { ?s a ?type }
        LIMIT 20
    """,
    ),
    (
        "Check specific node exists",
        """
        SELECT ?p ?o
        WHERE { <https://mathwiki.org/resource/def-group> ?p ?o }
    """,
    ),
    (
        "Count definitions directly",
        """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        SELECT (COUNT(?s) as ?count)
        WHERE { ?s a mymath:Definition }
    """,
    ),
]


def run_query(name, query):
    """Run a SPARQL query and print results"""
    print(f"\n{'='*60}")
    print(f"Query: {name}")
    print(f"{'='*60}")
    print(f"Query text:\n{query}")
    print("-" * 60)

    sparql = SPARQLWrapper(ENDPOINT)
    sparql.setQuery(query)
    sparql.setReturnFormat(JSON)

    try:
        results = sparql.query().convert()

        if "results" in results and "bindings" in results["results"]:
            bindings = results["results"]["bindings"]
            print(f"Found {len(bindings)} results:")

            for i, binding in enumerate(bindings):
                if i >= 5:  # Limit output for readability
                    print(f"  ... and {len(bindings) - 5} more results")
                    break
                row = []
                for var in results["head"]["vars"]:
                    if var in binding:
                        value = binding[var]["value"]
                        row.append(f"{var}: {value}")
                print(f"  {i+1}. " + " | ".join(row))
        else:
            print("No results found.")

    except Exception as e:
        print(f"Error executing query: {e}")


def main():
    print("Debugging SPARQL endpoint")
    print(f"Endpoint: {ENDPOINT}")

    for name, query in QUERIES:
        run_query(name, query)


if __name__ == "__main__":
    main()
