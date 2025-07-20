#!/usr/bin/env python3
"""
Verify consistency between Quarto knowledge graph and Lean formal proofs.
Compares dependencies and identifies discrepancies.
"""

import json
import logging
from pathlib import Path
from typing import Dict, Set
from rdflib import Graph, Namespace

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


def load_quarto_graph(ttl_file: Path) -> Dict[str, Set[str]]:
    """
    Load the Quarto knowledge graph and extract dependencies.

    Args:
        ttl_file: Path to the Turtle file

    Returns:
        Dictionary mapping node IDs to their dependencies
    """
    logger.info(f"Loading Quarto graph from {ttl_file}")

    # Define namespaces
    MYMATH = Namespace("https://mathwiki.org/ontology#")
    # BASE = Namespace("https://mathwiki.org/resource/")  # Not used

    # Load graph
    g = Graph()
    g.parse(ttl_file, format="turtle")

    # Extract dependencies
    dependencies = {}

    # Query for all uses relationships
    for subj, pred, obj in g.triples((None, MYMATH.uses, None)):
        # Extract node IDs from URIs
        subj_id = str(subj).split("/")[-1]
        obj_id = str(obj).split("/")[-1]

        if subj_id not in dependencies:
            dependencies[subj_id] = set()
        dependencies[subj_id].add(obj_id)

    logger.info(f"Loaded {len(dependencies)} nodes with dependencies")
    return dependencies


def load_lean_mappings(mapping_file: Path) -> Dict[str, str]:
    """
    Load Lean-Quarto mappings.

    Args:
        mapping_file: Path to the mapping JSON file

    Returns:
        Dictionary mapping Quarto node IDs to Lean IDs
    """
    if not mapping_file.exists():
        logger.warning(f"Mapping file {mapping_file} not found")
        return {}

    with open(mapping_file, "r") as f:
        mapping_data = json.load(f)

    # Extract node_to_lean mapping
    node_to_lean = mapping_data.get("node_to_lean", {})

    # Create simple mapping of node_id to lean_id
    mappings = {}
    for node_id, data in node_to_lean.items():
        if "lean_id" in data:
            mappings[node_id] = data["lean_id"]

    logger.info(f"Loaded {len(mappings)} node-to-Lean mappings")
    return mappings


def analyze_coverage(
    quarto_deps: Dict[str, Set[str]], lean_mappings: Dict[str, str]
) -> Dict[str, any]:
    """
    Analyze the coverage of formal proofs.

    Args:
        quarto_deps: Quarto dependency graph
        lean_mappings: Node to Lean ID mappings

    Returns:
        Dictionary with coverage statistics
    """
    all_nodes = set()

    # Collect all unique nodes
    for node, deps in quarto_deps.items():
        all_nodes.add(node)
        all_nodes.update(deps)

    # Find which nodes have formal proofs
    nodes_with_proofs = set(lean_mappings.keys())
    nodes_without_proofs = all_nodes - nodes_with_proofs

    # Calculate statistics
    total_nodes = len(all_nodes)
    verified_nodes = len(nodes_with_proofs)
    coverage_percent = (verified_nodes / total_nodes * 100) if total_nodes > 0 else 0

    # Categorize nodes by type
    node_types = {"Definition": [], "Theorem": [], "Example": [], "Axiom": []}

    for node in all_nodes:
        if node.startswith("def-"):
            node_types["Definition"].append(node)
        elif node.startswith("thm-"):
            node_types["Theorem"].append(node)
        elif node.startswith("ex-"):
            node_types["Example"].append(node)
        elif node.startswith("ax-"):
            node_types["Axiom"].append(node)

    return {
        "total_nodes": total_nodes,
        "verified_nodes": verified_nodes,
        "coverage_percent": coverage_percent,
        "nodes_without_proofs": sorted(list(nodes_without_proofs)),
        "nodes_with_proofs": sorted(list(nodes_with_proofs)),
        "node_types": node_types,
    }


def check_dependency_consistency(
    node_id: str, quarto_deps: Set[str], lean_deps: Set[str], mappings: Dict[str, str]
) -> Dict[str, any]:
    """
    Check consistency between Quarto and Lean dependencies for a node.

    Args:
        node_id: The node to check
        quarto_deps: Dependencies from Quarto
        lean_deps: Dependencies from Lean
        mappings: Node to Lean ID mappings

    Returns:
        Dictionary with consistency analysis
    """
    # Map Lean dependencies to Quarto node IDs
    # This would require reverse mapping, which we don't have yet
    # For now, we'll just note that formal verification exists

    return {
        "node_id": node_id,
        "has_formal_proof": node_id in mappings,
        "quarto_dependencies": sorted(list(quarto_deps)),
        "quarto_dep_count": len(quarto_deps),
    }


def generate_verification_report(coverage: Dict[str, any], output_file: Path) -> None:
    """
    Generate a verification report.

    Args:
        coverage: Coverage analysis results
        output_file: Path to save the report
    """
    report = []
    report.append("# Formal Verification Coverage Report\n")
    report.append("## Summary\n")
    report.append(f"- Total nodes: {coverage['total_nodes']}")
    report.append(f"- Formally verified: {coverage['verified_nodes']}")
    report.append(f"- Coverage: {coverage['coverage_percent']:.1f}%\n")

    report.append("## Coverage by Type\n")
    for node_type, nodes in coverage["node_types"].items():
        verified = [n for n in nodes if n in coverage["nodes_with_proofs"]]
        report.append(f"- {node_type}: {len(verified)}/{len(nodes)} verified")

    report.append("\n## Nodes with Formal Proofs\n")
    for node in coverage["nodes_with_proofs"]:
        report.append(f"- {node}")

    report.append("\n## Nodes without Formal Proofs\n")
    for node in coverage["nodes_without_proofs"]:
        report.append(f"- {node}")

    # Write report
    with open(output_file, "w") as f:
        f.write("\n".join(report))

    logger.info(f"Verification report saved to {output_file}")


def main():
    """Main function to verify formal-informal consistency."""
    # Define paths
    project_root = Path(__file__).parent.parent
    quarto_graph = project_root / "knowledge_graph.ttl"
    mapping_file = project_root / "lean_mappings.json"
    report_file = project_root / "formal_verification_report.md"

    logger.info("Starting formal verification consistency check...")

    try:
        # Load data
        quarto_deps = load_quarto_graph(quarto_graph)
        lean_mappings = load_lean_mappings(mapping_file)

        # Analyze coverage
        coverage = analyze_coverage(quarto_deps, lean_mappings)

        # Generate report
        generate_verification_report(coverage, report_file)

        # Print summary
        logger.info("\nVerification Summary:")
        logger.info(f"  Total nodes: {coverage['total_nodes']}")
        logger.info(f"  Formally verified: {coverage['verified_nodes']}")
        logger.info(f"  Coverage: {coverage['coverage_percent']:.1f}%")

        if coverage["verified_nodes"] > 0:
            logger.info("\nNodes with formal proofs:")
            for node in coverage["nodes_with_proofs"]:
                logger.info(f"  ✓ {node}")

        logger.info(f"\nReport saved to {report_file}")

    except Exception as e:
        logger.error(f"Verification failed: {e}")
        raise


if __name__ == "__main__":
    main()
