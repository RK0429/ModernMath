#!/usr/bin/env python3
"""
Extract dependency information from Lean 4 project using LeanDojo.
This script will parse the formal proofs and extract their dependency graph.
"""

import json
import logging
from pathlib import Path
from typing import Dict, List

# from lean_dojo import LeanGitRepo, trace  # For future use

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


def extract_lean_dependencies(repo_path: Path, output_dir: Path) -> Dict[str, List[str]]:
    """
    Extract dependencies from a Lean project using LeanDojo.

    Args:
        repo_path: Path to the Lean project
        output_dir: Directory to store trace output

    Returns:
        Dictionary mapping theorem names to their dependencies
    """
    logger.info(f"Extracting dependencies from {repo_path}")

    # Create output directory if it doesn't exist
    output_dir.mkdir(parents=True, exist_ok=True)

    try:
        # For now, we'll parse the Lean files directly
        # LeanDojo's trace feature requires a specific Git setup
        # which may not be available in our local project

        logger.info("Parsing Lean files directly...")
        dependencies = parse_lean_files_directly(repo_path)

        return dependencies

    except Exception as e:
        logger.error(f"Error extracting dependencies: {e}")
        raise


def parse_lean_files_directly(lean_dir: Path) -> Dict[str, List[str]]:
    """
    Parse Lean files directly to extract import dependencies.

    Args:
        lean_dir: Directory containing Lean files

    Returns:
        Dictionary mapping file names to their imports
    """
    dependencies = {}

    # Find all .lean files
    lean_files = list(lean_dir.rglob("*.lean"))
    logger.info(f"Found {len(lean_files)} Lean files")

    for lean_file in lean_files:
        # Skip lakefile.lean and other build files
        if lean_file.name in ["lakefile.lean", "lakefile.toml"]:
            continue

        # Get relative path from lean_dir
        rel_path = lean_file.relative_to(lean_dir)
        file_key = str(rel_path).replace(".lean", "").replace("/", ".")

        # Parse imports
        imports = []
        try:
            with open(lean_file, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith("import "):
                        import_name = line[7:].strip()
                        imports.append(import_name)
                    elif line and not line.startswith("--") and not line.startswith("/-"):
                        # Stop at first non-import, non-comment line
                        break

            if imports:
                dependencies[file_key] = imports
                logger.debug(f"{file_key}: {len(imports)} imports")

        except Exception as e:
            logger.warning(f"Error parsing {lean_file}: {e}")

    return dependencies


def parse_trace_output(trace_dir: Path) -> Dict[str, List[str]]:
    """
    Parse LeanDojo trace output to extract dependency information.

    Args:
        trace_dir: Directory containing trace output

    Returns:
        Dictionary mapping theorem names to their dependencies
    """
    dependencies = {}

    # Look for dependency files
    dep_files = list(trace_dir.glob("*.dep_paths"))
    if not dep_files:
        logger.warning("No dependency files found in trace output")
        return dependencies

    # Parse each dependency file
    for dep_file in dep_files:
        logger.info(f"Parsing {dep_file}")
        with open(dep_file, "r") as f:
            for line in f:
                if line.strip():
                    parts = line.strip().split(" : ")
                    if len(parts) == 2:
                        theorem = parts[0]
                        deps = parts[1].split(" ")
                        dependencies[theorem] = deps

    # Also look for XML trace files for more detailed information
    xml_files = list(trace_dir.glob("*.trace.xml"))
    for xml_file in xml_files:
        logger.info(f"Found XML trace file: {xml_file}")
        # TODO: Parse XML for more detailed theorem-level dependencies

    return dependencies


def map_lean_to_quarto(lean_deps: Dict[str, List[str]], mapping_file: Path) -> Dict[str, List[str]]:
    """
    Map Lean theorem names to Quarto node IDs.

    Args:
        lean_deps: Lean dependencies
        mapping_file: JSON file containing lean_id to node_id mappings

    Returns:
        Dependencies using Quarto node IDs
    """
    if not mapping_file.exists():
        logger.warning(f"Mapping file {mapping_file} not found")
        return {}

    with open(mapping_file, "r") as f:
        mapping_data = json.load(f)

    # Use the lean_to_node mapping directly
    lean_to_node = mapping_data.get("lean_to_node", {})

    # Create lean_to_quarto mapping from lean_to_node
    lean_to_quarto = {lean_id: data["node_id"] for lean_id, data in lean_to_node.items()}

    # Convert dependencies
    quarto_deps = {}
    for lean_theorem, lean_dependencies in lean_deps.items():
        if lean_theorem in lean_to_quarto:
            quarto_id = lean_to_quarto[lean_theorem]
            quarto_dep_list = []

            for lean_dep in lean_dependencies:
                if lean_dep in lean_to_quarto:
                    quarto_dep_list.append(lean_to_quarto[lean_dep])
                else:
                    logger.debug(f"No mapping found for Lean dependency: {lean_dep}")

            if quarto_dep_list:
                quarto_deps[quarto_id] = quarto_dep_list

    return quarto_deps


def generate_formal_graph_ttl(dependencies: Dict[str, List[str]], output_file: Path) -> None:
    """
    Generate RDF triples for formal dependencies.

    Args:
        dependencies: Dictionary of dependencies
        output_file: Path to output Turtle file
    """
    from rdflib import Graph, Namespace, RDFS, Literal

    # Define namespaces
    MYMATH = Namespace("https://mathwiki.org/ontology#")
    BASE = Namespace("https://mathwiki.org/resource/")

    # Create graph
    g = Graph()
    g.bind("mymath", MYMATH)
    g.bind("rdfs", RDFS)

    # Add triples for each dependency
    for theorem, deps in dependencies.items():
        theorem_uri = BASE[theorem]

        # Add formal verification marker
        g.add((theorem_uri, MYMATH.hasFormalProof, Literal(True)))

        # Add formal dependencies
        for dep in deps:
            dep_uri = BASE[dep]
            g.add((theorem_uri, MYMATH.formallyUses, dep_uri))

    # Serialize to Turtle
    g.serialize(destination=output_file, format="turtle")
    logger.info(f"Formal graph saved to {output_file}")


def main():
    """Main function to extract Lean dependencies."""
    # Define paths
    project_root = Path(__file__).parent.parent
    lean_project = project_root / "formal"
    output_dir = project_root / "lean_traces"
    mapping_file = project_root / "lean_mappings.json"
    formal_graph = project_root / "formal_graph.ttl"

    # Extract dependencies
    logger.info("Starting Lean dependency extraction...")

    try:
        # Extract raw Lean dependencies
        lean_deps = extract_lean_dependencies(lean_project, output_dir)
        logger.info(f"Extracted {len(lean_deps)} theorem dependencies")

        # Save raw dependencies
        raw_deps_file = output_dir / "raw_dependencies.json"
        with open(raw_deps_file, "w") as f:
            json.dump(lean_deps, f, indent=2)
        logger.info(f"Raw dependencies saved to {raw_deps_file}")

        # Map to Quarto IDs if mapping exists
        if mapping_file.exists():
            quarto_deps = map_lean_to_quarto(lean_deps, mapping_file)
            logger.info(f"Mapped {len(quarto_deps)} dependencies to Quarto IDs")

            # Generate formal graph
            generate_formal_graph_ttl(quarto_deps, formal_graph)
        else:
            logger.info("No mapping file found - skipping Quarto mapping")
            # Generate formal graph with Lean IDs
            generate_formal_graph_ttl(lean_deps, formal_graph)

        logger.info("Dependency extraction complete!")

    except Exception as e:
        logger.error(f"Failed to extract dependencies: {e}")
        raise


if __name__ == "__main__":
    main()
