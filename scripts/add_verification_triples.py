#!/usr/bin/env python3
"""
Add isVerifiedBy triples to the knowledge graph for formally verified nodes.
"""

import json
from pathlib import Path
from rdflib import Graph, Namespace, RDF, RDFS, Literal


def add_verification_triples() -> bool:
    """Add formal verification triples to the knowledge graph."""
    # Load the lean mappings
    mappings_path = Path("lean_mappings.json")
    if not mappings_path.exists():
        print(f"Error: {mappings_path} not found")
        return False

    with open(mappings_path) as f:
        mappings = json.load(f)

    # Load the existing knowledge graph
    graph_path = Path("knowledge_graph.ttl")
    if not graph_path.exists():
        print(f"Error: {graph_path} not found")
        return False

    g = Graph()
    g.parse(graph_path, format="turtle")
    print(f"Loaded knowledge graph with {len(g)} triples")

    # Define namespaces
    MYMATH = Namespace("https://mathwiki.org/ontology#")
    BASE = Namespace("https://mathwiki.org/resource/")

    # Bind namespaces for nice output
    g.bind("mymath", MYMATH)
    g.bind("base", BASE)

    # Add verification triples
    verified_count = 0
    for node_id, node_info in mappings.get("node_to_lean", {}).items():
        if "lean_id" in node_info:
            # Create URIs
            node_uri = BASE[node_id]

            # Create a formal proof node
            proof_uri = BASE[f"formal-proof-{node_id}"]

            # Add the formal proof node
            g.add((proof_uri, RDF.type, MYMATH.FormalProof))
            g.add((proof_uri, RDFS.label, Literal(f"Formal proof of {node_id}", lang="en")))
            g.add((proof_uri, MYMATH.inModule, Literal(node_info["lean_id"])))

            # Link the node to its formal proof
            g.add((node_uri, MYMATH.isVerifiedBy, proof_uri))

            # Add additional metadata
            if "module_name" in node_info:
                g.add(
                    (
                        proof_uri,
                        RDFS.comment,
                        Literal(f"Implemented in {node_info['module_name']}", lang="en"),
                    )
                )

            verified_count += 1
            print(f"  ✓ Added verification triple for {node_id} -> " f"{node_info['lean_id']}")

    print(f"\nAdded {verified_count} verification triples")
    print(f"Total triples after update: {len(g)}")

    # Save the updated graph
    g.serialize(destination=graph_path, format="turtle")
    print(f"\n✅ Updated knowledge graph saved to {graph_path}")

    return True


def main() -> None:
    """Main function."""
    print("Adding formal verification triples to knowledge graph...")

    if add_verification_triples():
        print("\n✅ Successfully added verification triples")
    else:
        print("\n❌ Failed to add verification triples")


if __name__ == "__main__":
    main()
