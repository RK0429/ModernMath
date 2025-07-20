#!/usr/bin/env python3
"""
PyVis Interactive Graph Visualization Module

This module provides functions to create interactive graph visualizations
for the Mathematics Knowledge Graph using the PyVis library.
"""

import json
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from pyvis.network import Network
from rdflib import Graph, Namespace, RDF, RDFS
from rdflib.namespace import SKOS
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Define namespaces
MYMATH = Namespace("https://mathwiki.org/ontology#")
BASE_URI = Namespace("https://mathwiki.org/resource/")

# Color scheme for different node types
NODE_COLORS = {
    "Definition": "#4CAF50",    # Green
    "Theorem": "#2196F3",       # Blue
    "Axiom": "#FF9800",         # Orange
    "Example": "#9C27B0",       # Purple
    "Lemma": "#00BCD4",         # Cyan
    "Proposition": "#3F51B5",   # Indigo
    "Corollary": "#009688",     # Teal
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


def load_knowledge_graph(ttl_path: Path) -> Graph:
    """Load the RDF knowledge graph from a Turtle file."""
    g = Graph()
    g.parse(ttl_path, format="turtle")
    return g


def get_node_info(g: Graph, node_uri: str) -> Dict[str, str]:
    """Extract information about a node from the graph."""
    node_uri_obj = BASE_URI[node_uri]
    
    # Get node type
    node_type = None
    for _, _, type_obj in g.triples((node_uri_obj, RDF.type, None)):
        type_str = str(type_obj).split("#")[-1]
        if type_str in NODE_COLORS:
            node_type = type_str
            break
    
    # Get node label
    label = node_uri
    for _, _, label_obj in g.triples((node_uri_obj, RDFS.label, None)):
        label = str(label_obj)
        break
    
    # Get domain
    domain = None
    for _, _, domain_obj in g.triples((node_uri_obj, MYMATH.hasDomain, None)):
        domain = str(domain_obj)
        break
    
    return {
        "id": node_uri,
        "label": label,
        "type": node_type or "Unknown",
        "domain": domain
    }


def get_neighbors(g: Graph, node_uri: str, depth: int = 2) -> Tuple[Set[str], List[Tuple[str, str, str]]]:
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
                    target_id = str(obj).split("/")[-1]
                    if target_id and target_id != current_uri:
                        edges.append((current_uri, target_id, "uses"))
                        to_visit.append((target_id, current_depth + 1))
            
            # Find all nodes that use this node (incoming edges)
            for subj, pred, _ in g.triples((None, None, current_uri_obj)):
                if str(pred) == str(MYMATH.uses):
                    source_id = str(subj).split("/")[-1]
                    if source_id and source_id != current_uri:
                        edges.append((source_id, current_uri, "uses"))
                        to_visit.append((source_id, current_depth + 1))
    
    return visited, edges


def create_local_graph(node_id: str, depth: int = 2, ttl_path: Path = Path("knowledge_graph.ttl")) -> Network:
    """
    Create an interactive graph visualization centered on a specific node.
    
    Args:
        node_id: The ID of the central node
        depth: How many hops away from the central node to include
        ttl_path: Path to the knowledge graph Turtle file
    
    Returns:
        A PyVis Network object
    """
    # Load the knowledge graph
    g = load_knowledge_graph(ttl_path)
    
    # Get neighbors and edges
    nodes, edges = get_neighbors(g, node_id, depth)
    
    # Create PyVis network
    net = Network(
        height="600px",
        width="100%",
        bgcolor="#ffffff",
        font_color="black",
        directed=True
    )
    
    # Configure physics
    net.set_options("""
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
    """)
    
    # Add nodes
    for node_uri in nodes:
        node_info = get_node_info(g, node_uri)
        
        # Determine if this is the central node
        is_central = node_uri == node_id
        
        # Add node with styling
        net.add_node(
            node_uri,
            label=node_info["label"],
            color=NODE_COLORS.get(node_info["type"], "#808080"),
            shape=NODE_SHAPES.get(node_info["type"], "ellipse"),
            size=30 if is_central else 20,
            borderWidth=3 if is_central else 1,
            borderWidthSelected=5,
            title=f"<b>{node_info['label']}</b><br>Type: {node_info['type']}<br>Domain: {node_info.get('domain', 'N/A')}<br>ID: {node_uri}"
        )
    
    # Add edges
    for source, target, rel_type in edges:
        if source in nodes and target in nodes:
            net.add_edge(
                source,
                target,
                title=rel_type,
                color="#999999",
                width=2
            )
    
    return net


def style_by_node_type(net: Network) -> Network:
    """Apply consistent styling based on node types."""
    # This is handled in create_local_graph, but kept for API compatibility
    return net


def add_hover_info(net: Network) -> Network:
    """Add hover information to nodes."""
    # This is handled in create_local_graph, but kept for API compatibility
    return net


def save_as_html(net: Network, filename: str, output_dir: Path = Path("output/interactive")) -> Path:
    """
    Save the network visualization as an HTML file.
    
    Args:
        net: The PyVis Network object
        filename: Name of the output file (without extension)
        output_dir: Directory to save the HTML file
    
    Returns:
        Path to the saved HTML file
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    output_path = output_dir / f"{filename}.html"
    
    # Configure PyVis to use CDN resources instead of local files
    net.cdn_resources = 'remote'
    net.save_graph(str(output_path))
    logger.info(f"Saved interactive graph to {output_path}")
    
    return output_path


def generate_all_node_graphs(ttl_path: Path = Path("knowledge_graph.ttl"), 
                           output_dir: Path = Path("output/interactive")) -> None:
    """Generate interactive graphs for all nodes in the knowledge graph."""
    g = load_knowledge_graph(ttl_path)
    
    # Get all nodes
    nodes = set()
    for subj, pred, _ in g.triples((None, RDF.type, None)):
        if str(pred) == str(RDF.type):
            node_id = str(subj).split("/")[-1]
            if node_id:
                nodes.add(node_id)
    
    logger.info(f"Generating interactive graphs for {len(nodes)} nodes...")
    
    # Generate graph for each node
    for i, node_id in enumerate(nodes, 1):
        try:
            net = create_local_graph(node_id, depth=2, ttl_path=ttl_path)
            save_as_html(net, node_id, output_dir)
            
            if i % 10 == 0:
                logger.info(f"Progress: {i}/{len(nodes)} graphs generated")
        except Exception as e:
            logger.error(f"Error generating graph for {node_id}: {e}")
    
    logger.info(f"Completed generating {len(nodes)} interactive graphs")


def create_domain_overview(domain: str, ttl_path: Path = Path("knowledge_graph.ttl")) -> Network:
    """Create an overview graph for all nodes in a specific mathematical domain."""
    g = load_knowledge_graph(ttl_path)
    
    # Find all nodes in the domain
    domain_nodes = set()
    for subj, _, domain_obj in g.triples((None, MYMATH.hasDomain, None)):
        if str(domain_obj).lower() == domain.lower():
            node_id = str(subj).split("/")[-1]
            if node_id:
                domain_nodes.add(node_id)
    
    # Create network
    net = Network(
        height="800px",
        width="100%",
        bgcolor="#ffffff",
        font_color="black",
        directed=True
    )
    
    # Configure physics for larger graphs
    net.set_options("""
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
    """)
    
    # Add nodes and collect edges
    edges = []
    for node_id in domain_nodes:
        node_info = get_node_info(g, node_id)
        
        net.add_node(
            node_id,
            label=node_info["label"],
            color=NODE_COLORS.get(node_info["type"], "#808080"),
            shape=NODE_SHAPES.get(node_info["type"], "ellipse"),
            size=25,
            title=f"<b>{node_info['label']}</b><br>Type: {node_info['type']}<br>ID: {node_id}"
        )
        
        # Get edges within the domain
        node_uri_obj = BASE_URI[node_id]
        for _, pred, obj in g.triples((node_uri_obj, MYMATH.uses, None)):
            target_id = str(obj).split("/")[-1]
            if target_id in domain_nodes:
                edges.append((node_id, target_id))
    
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
        net = create_local_graph(args.node, depth=args.depth)
        output_path = save_as_html(net, args.node)
        print(f"Generated interactive graph: {output_path}")
    elif args.domain:
        net = create_domain_overview(args.domain)
        output_path = save_as_html(net, f"domain-{args.domain.lower()}")
        print(f"Generated domain overview: {output_path}")
    elif args.all:
        generate_all_node_graphs()
    else:
        print("Please specify --node, --domain, or --all")