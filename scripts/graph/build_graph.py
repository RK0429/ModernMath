#!/usr/bin/env python3
"""
Build Knowledge Graph from Quarto Markdown Files

This script parses .qmd files in the content directory and builds an RDF graph
representing the mathematical knowledge structure.
"""

import json
import logging
import re
from pathlib import Path
from typing import Any, Dict, Optional

import frontmatter
import yaml
from rdflib import Graph, Literal, Namespace, RDF, RDFS, OWL, URIRef

from translation_graph import add_translation_edges

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

# Define namespaces
MYMATH = Namespace("https://mathwiki.org/ontology#")
BASE_URI = "https://mathwiki.org/resource/"
DCTERMS = Namespace("http://purl.org/dc/terms/")
SKOS = Namespace("http://www.w3.org/2004/02/skos/core#")

# Regex pattern to extract cross-references
CROSSREF_PATTERN = re.compile(r"@([a-zA-Z0-9_-]+)")


class KnowledgeGraphBuilder:  # pylint: disable=too-few-public-methods
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

    def _bind_namespaces(self) -> None:
        """Bind namespaces to the graph for cleaner serialization."""
        self.graph.bind("mymath", MYMATH)
        self.graph.bind("rdfs", RDFS)
        self.graph.bind("owl", OWL)
        self.graph.bind("dcterms", DCTERMS)
        self.graph.bind("skos", SKOS)

    def build(self) -> None:
        """Main method to build the knowledge graph."""
        logger.info("Starting knowledge graph construction from %s", self.content_dir)

        # First pass: collect all nodes
        qmd_files = list(self.content_dir.rglob("*.qmd"))
        logger.info("Found %d .qmd files", len(qmd_files))

        for qmd_path in qmd_files:
            self._process_file_first_pass(qmd_path)

        # Second pass: add relationships
        for qmd_path in qmd_files:
            self._process_file_second_pass(qmd_path)

        # Third pass: add Lean verification triples
        self._add_lean_verification_triples()

        # Save the graph
        self._save_graph()

    def _get_language_from_path(self, qmd_path: Path) -> str:
        """
        Detect the language of a file from its path.

        Args:
            qmd_path: Path to the .qmd file

        Returns:
            Language code ('en' or 'ja')
        """
        relative_path = qmd_path.relative_to(self.content_dir)

        # Check if path contains language directory
        if len(relative_path.parts) > 0 and relative_path.parts[0] in ["en", "ja"]:
            return str(relative_path.parts[0])

        # Default to English if no language directory found
        return "en"

    def _process_file_first_pass(self, qmd_path: Path) -> None:
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
                logger.warning("Skipping %s: missing required metadata (id or type)", qmd_path)
                return

            node_id = metadata["id"]
            node_uri = URIRef(BASE_URI + str(node_id))
            node_type = metadata["type"]

            # Detect the language of this file
            lang = self._get_language_from_path(qmd_path)

            # Register node only if not already registered
            if node_id not in self.node_registry:
                self.node_registry[node_id] = node_uri

                # Add node type (only needs to be added once)
                self.graph.add((node_uri, RDF.type, MYMATH[node_type]))

            # Add label with appropriate language tag
            if "title" in metadata:
                self.graph.add((node_uri, RDFS.label, Literal(metadata["title"], lang=lang)))

            # Add description from content (first paragraph) with language tag
            content_lines = post.content.strip().split("\n\n")
            if content_lines:
                first_paragraph = content_lines[0].strip()
                # Remove markdown headers
                first_paragraph = re.sub(
                    r"^#+\s+.*$", "", first_paragraph, flags=re.MULTILINE
                ).strip()
                if first_paragraph:
                    self.graph.add((node_uri, RDFS.comment, Literal(first_paragraph, lang=lang)))

            # Add domain if available (from directory metadata)
            domain = self._get_domain_from_path(qmd_path)
            if domain:
                self.graph.add((node_uri, MYMATH.hasDomain, Literal(domain)))

            # Add status
            if "status" in metadata:
                self.graph.add((node_uri, MYMATH.hasStatus, Literal(metadata["status"])))

            # Add Lean ID if available
            if "lean_id" in metadata:
                self.graph.add((node_uri, MYMATH.hasLeanId, Literal(metadata["lean_id"])))

            logger.info("Processed node: %s (%s) in %s", node_id, node_type, lang)

        except (KeyError, ValueError, TypeError) as e:
            logger.error("Error processing %s in first pass: %s", qmd_path, e)

    def _process_file_second_pass(self, qmd_path: Path) -> None:
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
                    logger.debug("Added relationship: %s uses %s", node_id, dep_id)
                else:
                    logger.warning("Unresolved reference: %s referenced by %s", dep_id, node_id)

        except (KeyError, ValueError, TypeError) as e:
            logger.error("Error processing %s in second pass: %s", qmd_path, e)

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
                        return str(dir_metadata["domain"])
            except (IOError, yaml.YAMLError) as e:
                logger.warning("Error reading %s: %s", metadata_path, e)

        # Fallback: use directory name as domain
        relative_path = qmd_path.relative_to(self.content_dir)

        # Handle multilingual structure: content/lang/domain/file.qmd
        if len(relative_path.parts) > 2 and relative_path.parts[0] in ["en", "ja"]:
            return str(relative_path.parts[1])
        if len(relative_path.parts) > 1:
            return str(relative_path.parts[0])

        return None

    def _add_lean_verification_triples(self) -> None:
        """Add isVerifiedBy triples for nodes that have formal Lean verification."""
        # Path to the Lean mappings file
        mappings_file = self.output_file.parent / "lean_mappings.json"

        if not mappings_file.exists():
            logger.info("No lean_mappings.json found, skipping Lean verification triples")
            return

        try:
            with open(mappings_file, "r", encoding="utf-8") as f:
                mappings_data = json.load(f)

            # Process node_to_lean mappings
            node_to_lean = mappings_data.get("node_to_lean", {})

            for node_id, lean_data in node_to_lean.items():
                self._process_lean_verification(node_id, lean_data)

            # Count how many nodes have verification
            verified_count = len(list(self.graph.triples((None, MYMATH.isVerifiedBy, None))))
            logger.info("Added %d Lean verification triples", verified_count)

        except (IOError, json.JSONDecodeError, KeyError) as e:
            logger.error("Error adding Lean verification triples: %s", e)

    def _process_lean_verification(self, node_id: str, lean_data: Dict[str, Any]) -> None:
        """Process a single Lean verification mapping."""
        if node_id not in self.node_registry:
            return

        node_uri = self.node_registry[node_id]
        lean_id = lean_data.get("lean_id")

        if not lean_id:
            return

        # Create a URI for the Lean proof
        lean_proof_uri = URIRef(f"https://mathlib.org/proof/{lean_id}")

        # Add the isVerifiedBy triple
        self.graph.add((node_uri, MYMATH.isVerifiedBy, lean_proof_uri))

        # Add metadata about the Lean proof
        self.graph.add((lean_proof_uri, RDF.type, MYMATH.FormalProof))

        # Get the label of the verified node to create a more descriptive label
        node_label = self._get_node_english_label(node_uri)

        if node_label:
            proof_label = f"Formal proof of {node_label}"
        else:
            proof_label = f"Formal proof of {node_id}"

        self.graph.add(
            (
                lean_proof_uri,
                RDFS.label,
                Literal(proof_label, lang="en"),
            )
        )

        # Add the module information
        if "module_name" in lean_data:
            self.graph.add((lean_proof_uri, MYMATH.inModule, Literal(lean_data["module_name"])))

        logger.info("Added Lean verification for %s -> %s", node_id, lean_id)

    def _get_node_english_label(self, node_uri: URIRef) -> Optional[str]:
        """Get the English label for a node URI."""
        for label in self.graph.objects(node_uri, RDFS.label):
            if isinstance(label, Literal) and label.language == "en":
                return str(label)
        return None

    def _save_graph(self) -> None:
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

        # Add translation edges if translation status file exists
        translation_status_file = self.content_dir.parent / "translations-status.yml"
        if translation_status_file.exists():
            add_translation_edges(self.graph, translation_status_file)
            logger.info("Added translation edges to the knowledge graph")

        # Serialize to Turtle format
        self.graph.serialize(destination=self.output_file, format="turtle")

        # Print statistics
        num_triples = len(self.graph)
        num_nodes = len(self.node_registry)
        num_relationships = len(list(self.graph.triples((None, MYMATH.uses, None))))

        logger.info("Knowledge graph saved to %s", self.output_file)
        logger.info("Statistics:")
        logger.info("  - Total triples: %d", num_triples)
        logger.info("  - Total nodes: %d", num_nodes)
        logger.info("  - Uses relationships: %d", num_relationships)


def main() -> None:
    """Main entry point."""
    # Set up paths
    project_root = Path(
        __file__
    ).parent.parent.parent  # Go up 3 levels: graph -> scripts -> project root
    content_dir = project_root / "content"
    output_file = project_root / "knowledge_graph.ttl"

    # Build the graph
    builder = KnowledgeGraphBuilder(content_dir, output_file)
    builder.build()


if __name__ == "__main__":
    main()
