#!/usr/bin/env python3
"""
PyVis Interactive Graph Visualization Module

This module provides functions to create interactive graph visualizations
for the Mathematics Knowledge Graph using the PyVis library.
"""

import json
import logging
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional, Any

from pyvis.network import Network
from rdflib import Graph, Namespace, RDF, RDFS
from rdflib.term import Literal

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Define namespaces
MYMATH = Namespace("https://mathwiki.org/ontology#")
BASE_URI = Namespace("https://mathwiki.org/resource/")

# Color scheme for different node types
NODE_COLORS = {
    "Definition": "#4CAF50",  # Green
    "Theorem": "#2196F3",  # Blue
    "Axiom": "#FF9800",  # Orange
    "Example": "#9C27B0",  # Purple
    "Lemma": "#00BCD4",  # Cyan
    "Proposition": "#3F51B5",  # Indigo
    "Corollary": "#009688",  # Teal
}

# Node shapes for different types
NODE_SHAPES = {
    "Definition": "box",
    "Theorem": "ellipse",
    "Axiom": "diamond",
    "Example": "square",
    "Lemma": "ellipse",
    "Proposition": "ellipse",
    "Corollary": "ellipse",
}

# Proof status icons for HTML display - only show check mark for completed proofs
PROOF_STATUS_ICONS = {
    "completed": "✔️",  # Simple check mark
}

PROOF_STATUS_DESCRIPTIONS = {
    "completed": "Formal proof completed",
}


def load_knowledge_graph(ttl_path: Path) -> Graph:
    """Load the RDF knowledge graph from a Turtle file."""
    g = Graph()
    g.parse(ttl_path, format="turtle")
    return g


def load_lean_data() -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """Load Lean mappings and validation results."""
    lean_mappings: Dict[str, Any] = {}
    lean_validation: Dict[str, Any] = {}

    # Load Lean mappings
    mappings_file = Path("lean_mappings.json")
    if mappings_file.exists():
        try:
            with open(mappings_file, "r", encoding="utf-8") as f:
                mappings_data = json.load(f)
                lean_mappings = mappings_data.get("node_to_lean", {})
        except (IOError, json.JSONDecodeError) as e:
            logger.warning("Could not load lean_mappings.json: %s", e)

    # Load Lean validation results
    validation_file = Path("lean_validation_results.json")
    if validation_file.exists():
        try:
            with open(validation_file, "r", encoding="utf-8") as f:
                validation_data = json.load(f)
                # Index by node_id for quick lookup
                for module_data in validation_data.get("modules", {}).values():
                    if module_data.get("node_id"):
                        lean_validation[module_data["node_id"]] = module_data["status"]
        except (IOError, json.JSONDecodeError) as e:
            logger.warning("Could not load lean_validation_results.json: %s", e)

    return lean_mappings, lean_validation


def get_node_info(g: Graph, node_uri: str, lang: str = "en") -> Dict[str, str]:
    """Extract information about a node from the graph with language preference."""
    node_uri_obj = BASE_URI[node_uri]

    # Get node type
    node_type = None
    for _, _, type_obj in g.triples((node_uri_obj, RDF.type, None)):
        type_str = str(type_obj).rsplit("#", maxsplit=1)[-1]
        if type_str in NODE_COLORS:
            node_type = type_str
            break

    # Get node label with language preference
    label = node_uri
    labels = {}
    for _, _, label_obj in g.triples((node_uri_obj, RDFS.label, None)):
        if isinstance(label_obj, Literal) and label_obj.language:
            labels[label_obj.language] = str(label_obj)
        else:
            labels["default"] = str(label_obj)

    # Select appropriate label
    if lang in labels:
        label = labels[lang]
    elif "en" in labels:
        label = labels["en"]
    elif "default" in labels:
        label = labels["default"]
    elif labels:
        label = next(iter(labels.values()))

    # Get domain
    domain = None
    for _, _, domain_obj in g.triples((node_uri_obj, MYMATH.hasDomain, None)):
        domain = str(domain_obj)
        break

    return {"id": node_uri, "label": label, "type": node_type or "Unknown", "domain": domain or ""}


def get_neighbors(
    g: Graph, node_uri: str, depth: int = 2
) -> Tuple[Set[str], List[Tuple[str, str, str]]]:
    """
    Get all nodes within a certain depth from the given node.
    Returns a set of node URIs and a list of edges (source, target, relationship).
    """
    visited = set()
    edges = []
    to_visit = [(node_uri, 0)]

    while to_visit:
        current_uri, current_depth = to_visit.pop(0)

        if current_uri in visited or current_depth > depth:
            continue

        visited.add(current_uri)
        current_uri_obj = BASE_URI[current_uri]

        if current_depth < depth:
            # Find all nodes this node uses (outgoing edges)
            for _, pred, obj in g.triples((current_uri_obj, None, None)):
                if str(pred) == str(MYMATH.uses):
                    target_id = str(obj).rsplit("/", maxsplit=1)[-1]
                    if target_id and target_id != current_uri:
                        edges.append((current_uri, target_id, "uses"))
                        to_visit.append((target_id, current_depth + 1))

            # Find all nodes that use this node (incoming edges)
            for subj, pred, _ in g.triples((None, None, current_uri_obj)):
                if str(pred) == str(MYMATH.uses):
                    source_id = str(subj).rsplit("/", maxsplit=1)[-1]
                    if source_id and source_id != current_uri:
                        edges.append((source_id, current_uri, "uses"))
                        to_visit.append((source_id, current_depth + 1))

    return visited, edges


def _create_network_with_physics() -> Network:
    """Create a PyVis network with standard physics configuration."""
    network = Network(
        height="600px", width="100%", bgcolor="#ffffff", font_color="black", directed=True
    )

    network.set_options(
        """
    {
        "physics": {
            "enabled": true,
            "solver": "forceAtlas2Based",
            "forceAtlas2Based": {
                "gravitationalConstant": -50,
                "centralGravity": 0.01,
                "springLength": 100,
                "springConstant": 0.08,
                "damping": 0.4
            }
        },
        "interaction": {
            "hover": true,
            "tooltipDelay": 300,
            "navigationButtons": true,
            "keyboard": true
        },
        "edges": {
            "arrows": {
                "to": {
                    "enabled": true,
                    "scaleFactor": 0.5
                }
            },
            "smooth": {
                "type": "curvedCW",
                "roundness": 0.2
            }
        }
    }
    """
    )
    return network


def _build_node_title(
    node_info: Dict[str, str],
    node_uri: str,
    lean_mappings: Optional[Dict[str, Any]],
    lean_validation: Optional[Dict[str, Any]],
    has_article: bool,
    lang: str,
) -> str:
    """Build the title/tooltip for a node."""
    title_parts = [
        f"<b>{node_info['label']}</b>",
        f"Type: {node_info['type']}",
        f"Domain: {node_info.get('domain', 'N/A')}",
        f"ID: {node_uri}",
    ]

    # Add proof status only if completed
    if lean_mappings and lean_validation and node_uri in lean_mappings:
        proof_status = lean_validation.get(node_uri, "not_implemented")
        # Only show proof status if it's completed
        if proof_status == "completed" and proof_status in PROOF_STATUS_ICONS:
            status_icon = PROOF_STATUS_ICONS[proof_status]
            status_desc = PROOF_STATUS_DESCRIPTIONS[proof_status]
            title_parts.append(f"Proof: {status_icon} {status_desc}")

    if has_article:
        # Add clickable link with appropriate language
        link_text = "記事を見る →" if lang == "ja" else "View Article →"
        title_parts.append("")  # Empty line for spacing
        title_parts.append(f"<a href='{node_uri}.html' target='_blank'>{link_text}</a>")

    return "<br>".join(title_parts)


def _has_article_prefix(node_uri: str) -> bool:
    """Check if a node URI has an article prefix."""
    return any(
        node_uri.startswith(prefix)
        for prefix in ["def-", "thm-", "ex-", "ax-", "prop-", "lem-", "cor-"]
    )


def create_local_graph(
    node_id: str,
    depth: int = 2,
    ttl_path: Path = Path("knowledge_graph.ttl"),
    lang: str = "en",
    lean_mappings: Optional[Dict[str, Any]] = None,
    lean_validation: Optional[Dict[str, Any]] = None,
) -> Network:
    """
    Create an interactive graph visualization centered on a specific node.

    Args:
        node_id: The ID of the central node
        depth: How many hops away from the central node to include
        ttl_path: Path to the knowledge graph Turtle file
        lang: Language preference for node labels
        lean_mappings: Optional Lean node mappings
        lean_validation: Optional Lean validation results

    Returns:
        A PyVis Network object
    """
    g = load_knowledge_graph(ttl_path)
    nodes, edges = get_neighbors(g, node_id, depth)
    network = _create_network_with_physics()

    # Add nodes
    for node_uri in nodes:
        node_info = get_node_info(g, node_uri, lang)
        is_central = node_uri == node_id
        has_article = _has_article_prefix(node_uri)

        title = _build_node_title(
            node_info, node_uri, lean_mappings, lean_validation, has_article, lang
        )

        # Add node with styling
        network.add_node(
            node_uri,
            label=node_info["label"],
            color=NODE_COLORS.get(node_info["type"], "#808080"),
            shape=NODE_SHAPES.get(node_info["type"], "ellipse"),
            size=30 if is_central else 20,
            borderWidth=3 if is_central else 1,
            borderWidthSelected=5,
            title=title,
        )

    # Add edges
    for source, target, rel_type in edges:
        if source in nodes and target in nodes:
            network.add_edge(source, target, title=rel_type, color="#999999", width=2)

    return network


def style_by_node_type(network: Network) -> Network:
    """Apply consistent styling based on node types."""
    # This is handled in create_local_graph, but kept for API compatibility
    return network


def add_hover_info(network: Network) -> Network:
    """Add hover information to nodes."""
    # This is handled in create_local_graph, but kept for API compatibility
    return network


def save_as_html(
    network: Network, filename: str, output_dir: Path = Path("output/interactive")
) -> Path:
    """
    Save the network visualization as an HTML file.

    Args:
        network: The PyVis Network object
        filename: Name of the output file (without extension)
        output_dir: Directory to save the HTML file

    Returns:
        Path to the saved HTML file
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    file_path = output_dir / f"{filename}.html"

    # Configure PyVis to use CDN resources instead of local files
    network.cdn_resources = "remote"
    network.save_graph(str(file_path))
    logger.info("Saved interactive graph to %s", file_path)

    return file_path


def generate_all_node_graphs(
    ttl_path: Path = Path("knowledge_graph.ttl"), output_dir: Path = Path("output/interactive")
) -> None:
    """Generate interactive graphs for all nodes in the knowledge graph."""
    g = load_knowledge_graph(ttl_path)

    # Load Lean data once for all graphs
    lean_mappings, lean_validation = load_lean_data()

    # Get all nodes
    nodes = set()
    for subj, pred, _ in g.triples((None, RDF.type, None)):
        if str(pred) == str(RDF.type):
            node_id = str(subj).rsplit("/", maxsplit=1)[-1]
            if node_id:
                nodes.add(node_id)

    logger.info("Generating interactive graphs for %d nodes...", len(nodes))

    # Generate graphs for each language
    for lang in ["en", "ja"]:
        lang_dir = output_dir / lang
        lang_dir.mkdir(parents=True, exist_ok=True)

        logger.info("Generating interactive graphs for language: %s", lang)

        # Generate graph for each node
        for i, node_id in enumerate(nodes, 1):
            try:
                graph_net = create_local_graph(
                    node_id,
                    depth=2,
                    ttl_path=ttl_path,
                    lang=lang,
                    lean_mappings=lean_mappings,
                    lean_validation=lean_validation,
                )
                save_as_html(graph_net, node_id, lang_dir)

                if i % 10 == 0:
                    logger.info("Progress (%s): %d/%d graphs generated", lang, i, len(nodes))
            except (IOError, ValueError, KeyError) as e:
                logger.error("Error generating graph for %s in %s: %s", node_id, lang, e)

        logger.info("Completed generating %d interactive graphs for %s", len(nodes), lang)

    logger.info("Completed generating all interactive graphs in both languages")


def _create_domain_network() -> Network:
    """Create a PyVis network configured for domain overview graphs."""
    net = Network(
        height="800px", width="100%", bgcolor="#ffffff", font_color="black", directed=True
    )

    net.set_options(
        """
    {
        "physics": {
            "enabled": true,
            "solver": "barnesHut",
            "barnesHut": {
                "gravitationalConstant": -2000,
                "centralGravity": 0.3,
                "springLength": 200,
                "springConstant": 0.04,
                "damping": 0.09
            }
        },
        "interaction": {
            "hover": true,
            "tooltipDelay": 300,
            "navigationButtons": true,
            "keyboard": true
        }
    }
    """
    )
    return net


def _find_domain_nodes(g: Graph, domain: str) -> Set[str]:
    """Find all nodes belonging to a specific domain."""
    domain_nodes = set()
    for subj, _, domain_obj in g.triples((None, MYMATH.hasDomain, None)):
        if str(domain_obj).lower() == domain.lower():
            node_id = str(subj).rsplit("/", maxsplit=1)[-1]
            if node_id:
                domain_nodes.add(node_id)
    return domain_nodes


def _collect_domain_edges(g: Graph, domain_nodes: Set[str]) -> List[Tuple[str, str]]:
    """Collect edges within a domain."""
    edges = []
    for node_id in domain_nodes:
        node_uri_obj = BASE_URI[node_id]
        for _, _, obj in g.triples((node_uri_obj, MYMATH.uses, None)):
            target_id = str(obj).rsplit("/", maxsplit=1)[-1]
            if target_id in domain_nodes:
                edges.append((node_id, target_id))
    return edges


def _build_domain_node_title(
    node_info: Dict[str, str],
    node_id: str,
    lean_mappings: Optional[Dict[str, Any]],
    lean_validation: Optional[Dict[str, Any]],
    has_article: bool,
    lang: str,
) -> str:
    """Build title for domain overview node."""
    title_parts = [
        f"<b>{node_info['label']}</b>",
        f"Type: {node_info['type']}",
        f"ID: {node_id}",
    ]

    # Add proof status only if completed
    if lean_mappings and lean_validation and node_id in lean_mappings:
        proof_status = lean_validation.get(node_id, "not_implemented")
        # Only show proof status if it's completed
        if proof_status == "completed" and proof_status in PROOF_STATUS_ICONS:
            status_icon = PROOF_STATUS_ICONS[proof_status]
            status_desc = PROOF_STATUS_DESCRIPTIONS[proof_status]
            title_parts.append(f"Proof: {status_icon} {status_desc}")

    if has_article:
        link_text = "記事を見る →" if lang == "ja" else "View Article →"
        title_parts.append("")  # Empty line
        title_parts.append(f"<a href='{node_id}.html' target='_blank'>{link_text}</a>")

    return "<br>".join(title_parts)


def create_domain_overview(
    domain: str,
    ttl_path: Path = Path("knowledge_graph.ttl"),
    lang: str = "en",
    lean_mappings: Optional[Dict[str, Any]] = None,
    lean_validation: Optional[Dict[str, Any]] = None,
) -> Network:
    """Create an overview graph for all nodes in a specific mathematical domain."""
    g = load_knowledge_graph(ttl_path)
    domain_nodes = _find_domain_nodes(g, domain)
    net = _create_domain_network()
    edges = _collect_domain_edges(g, domain_nodes)

    # Add nodes
    for node_id in domain_nodes:
        node_info = get_node_info(g, node_id, lang)
        has_article = _has_article_prefix(node_id)

        title = _build_domain_node_title(
            node_info, node_id, lean_mappings, lean_validation, has_article, lang
        )

        net.add_node(
            node_id,
            label=node_info["label"],
            color=NODE_COLORS.get(node_info["type"], "#808080"),
            shape=NODE_SHAPES.get(node_info["type"], "ellipse"),
            size=25,
            title=title,
        )

    # Add edges
    for source, target in edges:
        net.add_edge(source, target, color="#999999", width=2)

    return net


if __name__ == "__main__":
    # Example usage
    import argparse

    parser = argparse.ArgumentParser(description="Generate interactive graph visualizations")
    parser.add_argument("--node", help="Generate graph for a specific node")
    parser.add_argument("--domain", help="Generate overview for a specific domain")
    parser.add_argument("--all", action="store_true", help="Generate graphs for all nodes")
    parser.add_argument("--depth", type=int, default=2, help="Depth of neighborhood to include")

    args = parser.parse_args()

    if args.node:
        node_network = create_local_graph(args.node, depth=args.depth)
        result_path = save_as_html(node_network, args.node)
        print(f"Generated interactive graph: {result_path}")
    elif args.domain:
        domain_network = create_domain_overview(args.domain)
        result_path = save_as_html(domain_network, f"domain-{args.domain.lower()}")
        print(f"Generated domain overview: {result_path}")
    elif args.all:
        generate_all_node_graphs()
    else:
        print("Please specify --node, --domain, or --all")
