"""
Integration module for adding translation relationships to the RDF graph.
"""

from pathlib import Path
from rdflib import Graph, Namespace, URIRef, Literal
from rdflib.namespace import RDF, RDFS
import yaml


# Define namespaces
MATH = Namespace("http://modernmath.org/ontology#")


def add_translation_edges(graph: Graph, status_file: Path) -> None:
    """
    Add translation relationships to the RDF graph.

    Args:
        graph: RDF graph to modify
        status_file: Path to translations-status.yml
    """
    with open(status_file, "r", encoding="utf-8") as f:
        status_data = yaml.safe_load(f)

    # Add translation predicate if not exists
    graph.add((MATH.hasTranslation, RDF.type, RDF.Property))
    graph.add((MATH.hasTranslation, RDFS.label, Literal("has translation")))

    # Add edges for each translation
    for file_key, file_data in status_data["translations"].items():
        # Extract concept ID from file path (e.g., "algebra/def-group.qmd" -> "group")
        concept_id = (
            Path(file_key)
            .stem.replace("def-", "")
            .replace("thm-", "")
            .replace("ex-", "")
            .replace("ax-", "")
        )
        source_uri = URIRef(f"http://modernmath.org/concepts/{concept_id}")

        for lang, trans_data in file_data.get("translations", {}).items():
            if trans_data.get("status") == "completed":
                trans_uri = URIRef(f"http://modernmath.org/concepts/{concept_id}_{lang}")
                graph.add((source_uri, MATH.hasTranslation, trans_uri))
                graph.add((trans_uri, MATH.language, Literal(lang)))
