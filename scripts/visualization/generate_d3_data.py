#!/usr/bin/env python3
"""
Generate JSON data files for D3.js visualizations.
These files will be used by Observable JS in Quarto pages.
"""

import json
from pathlib import Path
from typing import Dict, Set, Tuple, Any, Optional

from rdflib import Graph, Literal, Namespace, RDF, RDFS

# Define namespaces
MYMATH = Namespace("https://mathwiki.org/ontology#")
BASE_URI = "https://mathwiki.org/resource/"
BASE_NS = Namespace(BASE_URI)


def _get_node_label(g: Graph, node_uri: Any, lang: str) -> Optional[str]:
    """Extract node label with language preference."""
    labels = {}
    for label in g.objects(node_uri, RDFS.label):
        if isinstance(label, Literal) and hasattr(label, "language") and label.language:
            labels[label.language] = str(label)
        else:
            labels["default"] = str(label)

    # Select appropriate label
    if lang in labels:
        return labels[lang]
    if "en" in labels:
        return labels["en"]
    if "default" in labels:
        return labels["default"]
    if labels:
        return next(iter(labels.values()))
    return None


def _get_node_type(g: Graph, node_uri: Any) -> Optional[str]:
    """Extract node type from RDF graph."""
    for node_type in g.objects(node_uri, RDF.type):
        if str(node_type).startswith(str(MYMATH)):
            return str(node_type).replace(str(MYMATH), "")
    return None


def _get_node_domain(g: Graph, node_uri: Any) -> Optional[str]:
    """Extract node domain from RDF graph."""
    for domain in g.objects(node_uri, MYMATH.hasDomain):
        domain_str = str(domain).lower().replace(" ", "-")
        # Handle special case for "Logic and Set Theory"
        if domain_str == "logic-and-set-theory":
            return "logic-set-theory"
        return domain_str
    return None


def _generate_node_url(node_id: str, domain: Optional[str]) -> Optional[str]:
    """Generate article URL for a node if applicable."""
    prefixes = ["def-", "thm-", "ex-", "ax-", "prop-", "lem-", "cor-"]
    if node_id and any(node_id.startswith(prefix) for prefix in prefixes):
        # For cross-domain navigation within the same language
        # From: /ModernMath/ja/content/ja/algebra/def-abelian-group.html
        # To:   /ModernMath/ja/content/ja/logic-set-theory/def-set.html
        # Path: ../logic-set-theory/def-set.html
        # (go up one level from algebra to ja, then into logic-set-theory)
        if domain:
            return f"../{domain}/{node_id}.html"
        # For nodes without domain (shouldn't happen), stay in current directory
        return f"{node_id}.html"
    return None


def get_node_info(g: Graph, node_uri: Any, lang: str = "en") -> Dict[str, Any]:
    """Get basic information about a node with language preference."""
    node_id = str(node_uri).replace(BASE_URI, "")

    # Extract node information using helper functions
    label = _get_node_label(g, node_uri, lang)
    node_type = _get_node_type(g, node_uri)
    domain = _get_node_domain(g, node_uri)
    url = _generate_node_url(node_id, domain)

    return {
        "id": node_id,
        "uri": str(node_uri),
        "label": label,
        "type": node_type,
        "url": url,
        "domain": domain,
    }


def get_node_neighbors(
    g: Graph, node_uri: Any, depth: int = 2
) -> Tuple[Set[Any], Set[Tuple[str, str]]]:
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


def create_d3_json(g: Graph, node_id: str, output_dir: Path, lang: str = "en") -> Path:
    """Create D3.js-compatible JSON for a specific node with language support."""
    node_uri = BASE_NS[node_id]

    # Get neighborhood
    neighbor_nodes, neighbor_edges = get_node_neighbors(g, node_uri, depth=2)

    # Build nodes array for D3
    nodes_data = []
    node_id_map = {}

    for i, n_uri in enumerate(neighbor_nodes):
        node_info = get_node_info(g, n_uri, lang=lang)
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


def get_domain_nodes_and_edges(g: Graph, domain: str) -> Tuple[Set[Any], Set[Tuple[str, str]]]:
    """Get all nodes and edges for a specific domain."""
    domain_nodes = set()

    # Find all nodes with this domain
    for s, _, o in g.triples((None, MYMATH.hasDomain, None)):
        if str(o).lower() == domain.lower():
            domain_nodes.add(s)

    # Get all edges between domain nodes
    domain_edges = set()
    for node in domain_nodes:
        for dep in g.objects(node, MYMATH.uses):
            if dep in domain_nodes:
                domain_edges.add((str(node), str(dep)))
        for dependent in g.subjects(MYMATH.uses, node):
            if dependent in domain_nodes:
                domain_edges.add((str(dependent), str(node)))

    return domain_nodes, domain_edges


def create_domain_json(g: Graph, domain: str, output_dir: Path, lang: str = "en") -> Path:
    """Create D3.js-compatible JSON for an entire domain with language support."""
    # Get domain nodes and edges
    domain_nodes, domain_edges = get_domain_nodes_and_edges(g, domain)

    # Build nodes array
    nodes_data = []
    node_id_map = {}

    for i, n_uri in enumerate(domain_nodes):
        node_info = get_node_info(g, n_uri, lang=lang)
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


def create_global_json(g: Graph, output_dir: Path, lang: str = "en") -> Path:
    """Create D3.js-compatible JSON for the entire knowledge graph."""
    # Get all nodes
    all_nodes = set()
    for s, _, o in g.triples((None, RDF.type, None)):
        if str(o).startswith(str(MYMATH)):
            all_nodes.add(s)

    # Get all edges
    all_edges = set()
    for node in all_nodes:
        for dep in g.objects(node, MYMATH.uses):
            if dep in all_nodes:
                all_edges.add((str(node), str(dep)))

    # Build nodes array
    nodes_data = []
    node_id_map = {}

    for i, n_uri in enumerate(all_nodes):
        node_info = get_node_info(g, n_uri, lang=lang)
        node_info["index"] = i
        nodes_data.append(node_info)
        node_id_map[str(n_uri)] = i

    # Build links array
    links_data = []
    for source_uri, target_uri in all_edges:
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
        "metadata": {
            "total_nodes": len(nodes_data),
            "total_links": len(links_data),
            "type": "global",
        },
    }

    # Save to JSON file
    output_file = output_dir / "global-graph.json"
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(d3_data, f, indent=2, ensure_ascii=False)

    return output_file


def main() -> None:
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
    for s, _, o in g.triples((None, RDF.type, None)):
        if str(o).startswith(str(MYMATH)):
            nodes.add(s)

    print(f"Found {len(nodes)} nodes in the graph")

    # Generate JSON for each node in each language
    print("Generating individual node data...")
    for lang in ["en", "ja"]:
        lang_dir = output_dir / lang
        lang_dir.mkdir(parents=True, exist_ok=True)
        print(f"\nGenerating {lang} data files...")

        for node_uri in nodes:
            # Extract node ID, handling both local and external URIs
            uri_str = str(node_uri)
            if uri_str.startswith(BASE_URI):
                node_id = uri_str.replace(BASE_URI, "")
            else:
                # For external URIs (like Lean), skip them for D3 generation
                continue

            if node_id and not node_id.startswith("index"):  # Skip index pages
                create_d3_json(g, node_id, lang_dir, lang=lang)

        print(f"  Generated {len(nodes)} {lang} node data files")

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

    for lang in ["en", "ja"]:
        lang_dir = output_dir / lang
        print(f"\nGenerating {lang} domain overview data...")
        for domain in domains:
            create_domain_json(g, domain, lang_dir, lang=lang)
            print(f"  Generated data for {domain} domain")

    # Generate global graph JSONs for both languages
    print("\nGenerating global graph data...")
    for lang in ["en", "ja"]:
        lang_dir = output_dir / lang
        create_global_json(g, lang_dir, lang=lang)
        print(f"  Generated global graph data for {lang}")

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

    with open(output_dir / "index.json", "w", encoding="utf-8") as f:
        json.dump(index_data, f, indent=2)

    print(f"\nGenerated {len(nodes)} individual node data files")
    print(f"Generated {len(domains)} domain overview data files")
    print(f"All D3.js data files saved to {output_dir}")


if __name__ == "__main__":
    main()
