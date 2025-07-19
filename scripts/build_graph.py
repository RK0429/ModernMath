#!/usr/bin/env python3
"""
Build Knowledge Graph from Quarto Markdown Files

This script parses .qmd files in the content directory and builds an RDF graph
representing the mathematical knowledge structure.
"""

import re
import yaml
from pathlib import Path
from typing import Dict, Optional
import logging

import frontmatter
from rdflib import Graph, Literal, Namespace, RDF, RDFS, OWL, URIRef

# Configure logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)

# Define namespaces
MYMATH = Namespace("https://mathwiki.org/ontology#")
BASE_URI = "https://mathwiki.org/resource/"
DCTERMS = Namespace("http://purl.org/dc/terms/")
SKOS = Namespace("http://www.w3.org/2004/02/skos/core#")

# Regex pattern to extract cross-references
CROSSREF_PATTERN = re.compile(r"@([a-zA-Z0-9_-]+)")


class KnowledgeGraphBuilder:
    """Build RDF knowledge graph from Quarto content files."""

    def __init__(self, content_dir: Path, output_file: Path):
        """
        Initialize the knowledge graph builder.

        Args:
            content_dir: Path to the content directory containing .qmd files
            output_file: Path where the output .ttl file will be saved
        """
        self.content_dir = content_dir
        self.output_file = output_file
        self.graph = Graph()
        self._bind_namespaces()
        self.node_registry: Dict[str, URIRef] = {}

    def _bind_namespaces(self):
        """Bind namespaces to the graph for cleaner serialization."""
        self.graph.bind("mymath", MYMATH)
        self.graph.bind("rdfs", RDFS)
        self.graph.bind("owl", OWL)
        self.graph.bind("dcterms", DCTERMS)
        self.graph.bind("skos", SKOS)

    def build(self):
        """Main method to build the knowledge graph."""
        logger.info(f"Starting knowledge graph construction from {self.content_dir}")

        # First pass: collect all nodes
        qmd_files = list(self.content_dir.rglob("*.qmd"))
        logger.info(f"Found {len(qmd_files)} .qmd files")

        for qmd_path in qmd_files:
            self._process_file_first_pass(qmd_path)

        # Second pass: add relationships
        for qmd_path in qmd_files:
            self._process_file_second_pass(qmd_path)

        # Save the graph
        self._save_graph()

    def _process_file_first_pass(self, qmd_path: Path):
        """
        First pass: Extract node information and register in the graph.

        Args:
            qmd_path: Path to the .qmd file
        """
        try:
            with open(qmd_path, "r", encoding="utf-8") as f:
                post = frontmatter.load(f)

            metadata = post.metadata

            # Skip files without required metadata
            if "id" not in metadata or "type" not in metadata:
                logger.warning(
                    f"Skipping {qmd_path}: missing required metadata (id or type)"
                )
                return

            node_id = metadata["id"]
            node_uri = URIRef(BASE_URI + node_id)
            self.node_registry[node_id] = node_uri

            # Add node type
            node_type = metadata["type"]
            self.graph.add((node_uri, RDF.type, MYMATH[node_type]))

            # Add label
            if "title" in metadata:
                self.graph.add(
                    (node_uri, RDFS.label, Literal(metadata["title"], lang="en"))
                )

            # Add description from content (first paragraph)
            content_lines = post.content.strip().split("\n\n")
            if content_lines:
                first_paragraph = content_lines[0].strip()
                # Remove markdown headers
                first_paragraph = re.sub(
                    r"^#+\s+.*$", "", first_paragraph, flags=re.MULTILINE
                ).strip()
                if first_paragraph:
                    self.graph.add(
                        (node_uri, RDFS.comment, Literal(first_paragraph, lang="en"))
                    )

            # Add domain if available (from directory metadata)
            domain = self._get_domain_from_path(qmd_path)
            if domain:
                self.graph.add((node_uri, MYMATH.hasDomain, Literal(domain)))

            # Add status
            if "status" in metadata:
                self.graph.add(
                    (node_uri, MYMATH.hasStatus, Literal(metadata["status"]))
                )

            # Add Lean ID if available
            if "lean_id" in metadata:
                self.graph.add(
                    (node_uri, MYMATH.hasLeanId, Literal(metadata["lean_id"]))
                )

            logger.info(f"Registered node: {node_id} ({node_type})")

        except Exception as e:
            logger.error(f"Error processing {qmd_path} in first pass: {e}")

    def _process_file_second_pass(self, qmd_path: Path):
        """
        Second pass: Extract and add relationships between nodes.

        Args:
            qmd_path: Path to the .qmd file
        """
        try:
            with open(qmd_path, "r", encoding="utf-8") as f:
                post = frontmatter.load(f)

            metadata = post.metadata
            content = post.content

            if "id" not in metadata:
                return

            node_id = metadata["id"]
            node_uri = self.node_registry.get(node_id)

            if not node_uri:
                return

            # Extract dependencies from cross-references in content
            dependencies = set(CROSSREF_PATTERN.findall(content))

            # Add dependencies from YAML 'requires' field
            if "requires" in metadata and isinstance(metadata["requires"], list):
                dependencies.update(metadata["requires"])

            # Add dependency relationships
            for dep_id in dependencies:
                if dep_id in self.node_registry:
                    dep_uri = self.node_registry[dep_id]
                    self.graph.add((node_uri, MYMATH.uses, dep_uri))
                    logger.debug(f"Added relationship: {node_id} uses {dep_id}")
                else:
                    logger.warning(
                        f"Unresolved reference: {dep_id} referenced by {node_id}"
                    )

        except Exception as e:
            logger.error(f"Error processing {qmd_path} in second pass: {e}")

    def _get_domain_from_path(self, qmd_path: Path) -> Optional[str]:
        """
        Extract domain from directory structure or _metadata.yml.

        Args:
            qmd_path: Path to the .qmd file

        Returns:
            Domain name if found, None otherwise
        """
        # Check for _metadata.yml in the same directory
        metadata_path = qmd_path.parent / "_metadata.yml"
        if metadata_path.exists():
            try:
                with open(metadata_path, "r", encoding="utf-8") as f:
                    dir_metadata = yaml.safe_load(f)
                    if dir_metadata and "domain" in dir_metadata:
                        return dir_metadata["domain"]
            except Exception as e:
                logger.warning(f"Error reading {metadata_path}: {e}")

        # Fallback: use directory name as domain
        relative_path = qmd_path.relative_to(self.content_dir)
        if len(relative_path.parts) > 1:
            return relative_path.parts[0]

        return None

    def _save_graph(self):
        """Save the graph to a Turtle file."""
        # Add ontology metadata
        ontology_uri = URIRef("https://mathwiki.org/ontology")
        self.graph.add((ontology_uri, RDF.type, OWL.Ontology))
        self.graph.add(
            (
                ontology_uri,
                RDFS.label,
                Literal("Mathematics Knowledge Graph Ontology", lang="en"),
            )
        )
        self.graph.add(
            (
                ontology_uri,
                RDFS.comment,
                Literal(
                    "An ontology for representing mathematical knowledge as a graph",
                    lang="en",
                ),
            )
        )

        # Serialize to Turtle format
        self.graph.serialize(destination=self.output_file, format="turtle")

        # Print statistics
        num_triples = len(self.graph)
        num_nodes = len(self.node_registry)
        num_relationships = len(list(self.graph.triples((None, MYMATH.uses, None))))

        logger.info(f"Knowledge graph saved to {self.output_file}")
        logger.info("Statistics:")
        logger.info(f"  - Total triples: {num_triples}")
        logger.info(f"  - Total nodes: {num_nodes}")
        logger.info(f"  - Uses relationships: {num_relationships}")


def main():
    """Main entry point."""
    # Set up paths
    project_root = Path(__file__).parent.parent
    content_dir = project_root / "content"
    output_file = project_root / "knowledge_graph.ttl"

    # Build the graph
    builder = KnowledgeGraphBuilder(content_dir, output_file)
    builder.build()


if __name__ == "__main__":
    main()
