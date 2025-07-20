#!/usr/bin/env python3
"""
Generate JSON data files for D3.js visualizations.
These files will be used by Observable JS in Quarto pages.
"""

import json
from pathlib import Path
from rdflib import Graph, Namespace, RDF, RDFS
from typing import Dict, Set, Tuple

# Define namespaces
MYMATH = Namespace("https://mathwiki.org/ontology#")
BASE_URI = "https://mathwiki.org/resource/"
BASE_NS = Namespace(BASE_URI)


def get_node_info(g: Graph, node_uri) -> Dict:
    """Get basic information about a node."""
    info = {
        "id": str(node_uri).replace(BASE_URI, ""),
        "uri": str(node_uri),
        "label": None,
        "type": None,
    }

    # Get label
    for label in g.objects(node_uri, RDFS.label):
        info["label"] = str(label)
        break

    # Get type
    for node_type in g.objects(node_uri, RDF.type):
        if str(node_type).startswith(str(MYMATH)):
            info["type"] = str(node_type).replace(str(MYMATH), "")
            break

    return info


def get_node_neighbors(g: Graph, node_uri, depth: int = 2) -> Tuple[Set, Set]:
    """Get neighbors of a node up to specified depth."""
    nodes = {node_uri}
    edges = set()

    current_level = {node_uri}

    for _ in range(depth):
        next_level = set()

        for current_node in current_level:
            # Get nodes this node depends on (outgoing edges)
            for dep in g.objects(current_node, MYMATH.uses):
                edges.add((str(current_node), str(dep)))
                nodes.add(dep)
                next_level.add(dep)

            # Get nodes that depend on this node (incoming edges)
            for dependent in g.subjects(MYMATH.uses, current_node):
                edges.add((str(dependent), str(current_node)))
                nodes.add(dependent)
                next_level.add(dependent)

        current_level = next_level

    return nodes, edges


def create_d3_json(g: Graph, node_id: str, output_dir: Path):
    """Create D3.js-compatible JSON for a specific node."""
    node_uri = BASE_NS[node_id]

    # Get neighborhood
    neighbor_nodes, neighbor_edges = get_node_neighbors(g, node_uri, depth=2)

    # Build nodes array for D3
    nodes_data = []
    node_id_map = {}

    for i, n_uri in enumerate(neighbor_nodes):
        node_info = get_node_info(g, n_uri)
        node_info["index"] = i
        node_info["is_focus"] = str(n_uri) == str(node_uri)
        nodes_data.append(node_info)
        node_id_map[str(n_uri)] = i

    # Build links array for D3
    links_data = []
    for source_uri, target_uri in neighbor_edges:
        if source_uri in node_id_map and target_uri in node_id_map:
            links_data.append(
                {
                    "source": node_id_map[source_uri],
                    "target": node_id_map[target_uri],
                    "type": "uses",
                }
            )

    # Create the final data structure
    d3_data = {
        "nodes": nodes_data,
        "links": links_data,
        "focus_node": node_id,
        "metadata": {
            "total_nodes": len(nodes_data),
            "total_links": len(links_data),
            "depth": 2,
        },
    }

    # Save to JSON file
    output_file = output_dir / f"{node_id}.json"
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(d3_data, f, indent=2, ensure_ascii=False)

    return output_file


def create_domain_json(g: Graph, domain: str, output_dir: Path):
    """Create D3.js-compatible JSON for an entire domain."""
    # Query for all nodes in this domain
    domain_nodes = set()
    domain_edges = set()

    # Find all nodes with this domain
    for s, p, o in g.triples((None, MYMATH.hasDomain, None)):
        if str(o).lower() == domain.lower():
            domain_nodes.add(s)

    # Get all edges between domain nodes
    for node in domain_nodes:
        for dep in g.objects(node, MYMATH.uses):
            if dep in domain_nodes:
                domain_edges.add((str(node), str(dep)))
        for dependent in g.subjects(MYMATH.uses, node):
            if dependent in domain_nodes:
                domain_edges.add((str(dependent), str(node)))

    # Build nodes array
    nodes_data = []
    node_id_map = {}

    for i, n_uri in enumerate(domain_nodes):
        node_info = get_node_info(g, n_uri)
        node_info["index"] = i
        nodes_data.append(node_info)
        node_id_map[str(n_uri)] = i

    # Build links array
    links_data = []
    for source_uri, target_uri in domain_edges:
        if source_uri in node_id_map and target_uri in node_id_map:
            links_data.append(
                {
                    "source": node_id_map[source_uri],
                    "target": node_id_map[target_uri],
                    "type": "uses",
                }
            )

    # Create the final data structure
    d3_data = {
        "nodes": nodes_data,
        "links": links_data,
        "domain": domain,
        "metadata": {"total_nodes": len(nodes_data), "total_links": len(links_data)},
    }

    # Save to JSON file
    output_file = output_dir / f"domain-{domain.lower().replace(' ', '-')}.json"
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(d3_data, f, indent=2, ensure_ascii=False)

    return output_file


def main():
    """Main function to generate all D3.js data files."""
    # Load the knowledge graph
    print("Loading knowledge graph...")
    g = Graph()
    g.parse("knowledge_graph.ttl", format="turtle")

    # Create output directory
    output_dir = Path("output/d3-data")
    output_dir.mkdir(parents=True, exist_ok=True)

    # Get all nodes
    nodes = set()
    for s, p, o in g.triples((None, RDF.type, None)):
        if str(o).startswith(str(MYMATH)):
            nodes.add(s)

    print(f"Found {len(nodes)} nodes in the graph")

    # Generate JSON for each node
    print("Generating individual node data...")
    for node_uri in nodes:
        # Extract node ID, handling both local and external URIs
        uri_str = str(node_uri)
        if uri_str.startswith(BASE_URI):
            node_id = uri_str.replace(BASE_URI, "")
        else:
            # For external URIs (like Lean), skip them for D3 generation
            continue

        if node_id and not node_id.startswith("index"):  # Skip index pages
            create_d3_json(g, node_id, output_dir)
            print(f"  Generated data for {node_id}")

    # Generate domain overview JSONs
    print("\nGenerating domain overview data...")
    domains = [
        "Algebra",
        "Analysis",
        "Topology",
        "Number Theory",
        "Logic and Set Theory",
        "Geometry",
        "Category Theory",
        "Combinatorics",
        "Probability and Statistics",
    ]

    for domain in domains:
        create_domain_json(g, domain, output_dir)
        print(f"  Generated data for {domain} domain")

    # Create an index file
    valid_nodes = []
    for n in nodes:
        uri_str = str(n)
        if uri_str.startswith(BASE_URI) and not uri_str.endswith("index"):
            valid_nodes.append(uri_str.replace(BASE_URI, ""))

    index_data = {
        "nodes": valid_nodes,
        "domains": [d.lower().replace(" ", "-") for d in domains],
    }

    with open(output_dir / "index.json", "w") as f:
        json.dump(index_data, f, indent=2)

    print(f"\nGenerated {len(nodes)} individual node data files")
    print(f"Generated {len(domains)} domain overview data files")
    print(f"All D3.js data files saved to {output_dir}")


if __name__ == "__main__":
    main()
