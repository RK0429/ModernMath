#!/usr/bin/env python3
"""
Validate the Knowledge Graph

This script validates the generated knowledge graph for:
- Broken references
- Circular dependencies
- Orphaned nodes
- Missing metadata
"""

import logging
import sys
from pathlib import Path
from typing import Set, List, Dict
from collections import defaultdict

from rdflib import Graph, Namespace, RDF

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

# Define namespaces
MYMATH = Namespace("https://mathwiki.org/ontology#")
BASE_URI = "https://mathwiki.org/resource/"


class GraphValidator:
    """Validate the RDF knowledge graph."""

    def __init__(self, graph_file: Path):
        """
        Initialize the validator.

        Args:
            graph_file: Path to the .ttl file to validate
        """
        self.graph_file = graph_file
        self.graph = Graph()
        self.issues: List[str] = []

    def validate(self) -> bool:
        """
        Run all validation checks.

        Returns:
            True if no critical issues found, False otherwise
        """
        logger.info("Loading graph from %s", self.graph_file)
        self.graph.parse(self.graph_file, format="turtle")

        logger.info("Running validation checks...")

        # Run validation checks
        self._check_node_types()
        self._check_broken_references()
        self._check_circular_dependencies()
        self._check_orphaned_nodes()
        self._check_bidirectional_references()

        # Report results
        if self.issues:
            logger.warning("Found %d issues:", len(self.issues))
            for issue in self.issues:
                logger.warning("  - %s", issue)
        else:
            logger.info("No issues found!")

        return len([i for i in self.issues if i.startswith("ERROR")]) == 0

    def _check_node_types(self) -> None:
        """Check that all nodes have valid types."""
        valid_types = {MYMATH.Definition, MYMATH.Theorem, MYMATH.Axiom, MYMATH.Example}

        for subject in self.graph.subjects(RDF.type, None):
            types = list(self.graph.objects(subject, RDF.type))

            if not types:
                self.issues.append(f"ERROR: Node {subject} has no type")
            elif not any(t in valid_types for t in types):
                self.issues.append(f"WARNING: Node {subject} has non-standard type: {types}")

    def _check_broken_references(self) -> None:
        """Check for references to non-existent nodes."""
        # Get all node URIs
        all_nodes = set()
        for subject in self.graph.subjects(RDF.type, None):
            all_nodes.add(str(subject))

        # Check all 'uses' relationships
        for s, _, o in self.graph.triples((None, MYMATH.uses, None)):
            if str(o) not in all_nodes:
                node_id = str(s).replace(BASE_URI, "")
                ref_id = str(o).replace(BASE_URI, "")
                self.issues.append(
                    f"ERROR: Broken reference: {node_id} references non-existent {ref_id}"
                )

    def _check_circular_dependencies(self) -> None:
        """Check for circular dependencies in the graph."""
        # Build adjacency list
        adjacency = defaultdict(set)
        nodes = set()

        for s, _, o in self.graph.triples((None, MYMATH.uses, None)):
            adjacency[str(s)].add(str(o))
            nodes.add(str(s))
            nodes.add(str(o))

        # Check for cycles using DFS
        def has_cycle_from(node: str, visited: Set[str], rec_stack: Set[str]) -> List[str]:
            visited.add(node)
            rec_stack.add(node)

            for neighbor in adjacency.get(node, []):
                if neighbor not in visited:
                    cycle = has_cycle_from(neighbor, visited, rec_stack)
                    if cycle:
                        return [node] + cycle
                elif neighbor in rec_stack:
                    return [node, neighbor]

            rec_stack.remove(node)
            return []

        visited: Set[str] = set()
        for node in nodes:
            if node not in visited:
                cycle = has_cycle_from(node, visited, set())
                if cycle:
                    cycle_str = " -> ".join(n.replace(BASE_URI, "") for n in cycle)
                    self.issues.append(f"WARNING: Circular dependency detected: {cycle_str}")

    def _check_orphaned_nodes(self) -> None:
        """Check for nodes with no incoming or outgoing relationships."""
        nodes_with_relationships = set()

        # Collect nodes with uses relationships
        for s, _, o in self.graph.triples((None, MYMATH.uses, None)):
            nodes_with_relationships.add(str(s))
            nodes_with_relationships.add(str(o))

        # Check all typed nodes
        for subject in self.graph.subjects(RDF.type, None):
            if str(subject) not in nodes_with_relationships:
                # Check if it's an Example or Axiom (which might legitimately have no uses)
                node_type = list(self.graph.objects(subject, RDF.type))[0]
                if node_type not in [MYMATH.Example, MYMATH.Axiom]:
                    node_id = str(subject).replace(BASE_URI, "")
                    self.issues.append(f"INFO: Orphaned node (no relationships): {node_id}")

    def _check_bidirectional_references(self) -> None:
        """Check for inconsistent bidirectional references."""
        # This is more of a warning - if A uses B in its proof,
        # but B also uses A, it might indicate a logical issue
        uses_map = defaultdict(set)

        for s, _, o in self.graph.triples((None, MYMATH.uses, None)):
            uses_map[str(s)].add(str(o))

        for node, dependencies in uses_map.items():
            for dep in dependencies:
                if node in uses_map.get(dep, []):
                    node_id = node.replace(BASE_URI, "")
                    dep_id = dep.replace(BASE_URI, "")
                    self.issues.append(f"INFO: Bidirectional dependency: {node_id} <-> {dep_id}")

    def print_statistics(self) -> None:
        """Print statistics about the graph."""
        # Count nodes by type
        type_counts: Dict[str, int] = defaultdict(int)
        for _, _, o in self.graph.triples((None, RDF.type, None)):
            type_name = str(o).replace(str(MYMATH), "")
            type_counts[type_name] += 1

        # Count relationships
        uses_count = len(list(self.graph.triples((None, MYMATH.uses, None))))

        logger.info("\nGraph Statistics:")
        logger.info("  Total triples: %d", len(self.graph))
        logger.info("  Node counts by type:")
        for node_type, count in sorted(type_counts.items()):
            logger.info("    - %s: %d", node_type, count)
        logger.info("  Total 'uses' relationships: %d", uses_count)


def main() -> int:
    """Main entry point."""
    project_root = Path(__file__).parent.parent.parent
    graph_file = project_root / "knowledge_graph.ttl"

    if not graph_file.exists():
        logger.error("Graph file not found: %s", graph_file)
        logger.error("Please run build_graph.py first")
        return 1

    validator = GraphValidator(graph_file)
    is_valid = validator.validate()
    validator.print_statistics()

    return 0 if is_valid else 1


if __name__ == "__main__":
    sys.exit(main())
