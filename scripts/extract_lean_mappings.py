#!/usr/bin/env python3
"""
Extract mappings between Lean formal proofs and Quarto content nodes.
Parses Lean files to find Node ID and Lean ID references in comments.
"""

import json
import logging
import re
from pathlib import Path
from typing import Any, Dict, List, Optional

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


def extract_metadata_from_lean_file(file_path: Path) -> Optional[Dict[str, str]]:
    """
    Extract metadata from a Lean file's comments.

    Looks for patterns like:
    * Node ID: def-group
    * Quarto file: content/algebra/def-group.qmd
    * Lean ID: Mathlib.Algebra.Group.Defs.Group

    Args:
        file_path: Path to Lean file

    Returns:
        Dictionary with metadata or None if not found
    """
    metadata = {}

    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        # Extract Node ID
        node_match = re.search(r"\* Node ID:\s*([a-zA-Z0-9-_]+)", content)
        if node_match:
            metadata["node_id"] = node_match.group(1)

        # Extract Quarto file path
        quarto_match = re.search(r"\* Quarto file:\s*([^\n]+)", content)
        if quarto_match:
            metadata["quarto_file"] = quarto_match.group(1).strip()

        # Extract Lean ID
        lean_match = re.search(r"\* Lean ID:\s*([a-zA-Z0-9._]+)", content)
        if lean_match:
            metadata["lean_id"] = lean_match.group(1)

        # Get the module name from the file path
        rel_path = file_path.relative_to(file_path.parent.parent.parent)
        module_name = str(rel_path).replace(".lean", "").replace("/", ".")
        metadata["module_name"] = module_name

        return metadata if metadata else None

    except (IOError, OSError) as e:
        logger.warning("Error reading %s: %s", file_path, e)
        return None


def extract_all_mappings(lean_dir: Path) -> List[Dict[str, str]]:
    """
    Extract mappings from all Lean files in a directory.

    Args:
        lean_dir: Directory containing Lean files

    Returns:
        List of mapping dictionaries
    """
    mappings = []

    # Find all .lean files
    lean_files = list(lean_dir.rglob("*.lean"))
    logger.info("Scanning %d Lean files for mappings...", len(lean_files))

    for lean_file in lean_files:
        # Skip build files
        if lean_file.name in ["lakefile.lean", "Main.lean"]:
            continue

        metadata = extract_metadata_from_lean_file(lean_file)
        if metadata is not None:
            if "node_id" in metadata:
                mappings.append(metadata)
                logger.info(
                    "Found mapping: %s -> %s", metadata["node_id"], metadata.get("lean_id", "N/A")
                )

    return mappings


def create_bidirectional_mapping(mappings: List[Dict[str, str]]) -> Dict[str, Any]:
    """
    Create bidirectional mapping dictionaries.

    Args:
        mappings: List of mapping dictionaries

    Returns:
        Dictionary with 'node_to_lean' and 'lean_to_node' mappings
    """
    node_to_lean = {}
    lean_to_node = {}

    for mapping in mappings:
        node_id = mapping.get("node_id")
        lean_id = mapping.get("lean_id")

        if node_id and lean_id:
            node_to_lean[node_id] = {
                "lean_id": lean_id,
                "module_name": mapping.get("module_name"),
                "quarto_file": mapping.get("quarto_file"),
            }

            lean_to_node[lean_id] = {
                "node_id": node_id,
                "module_name": mapping.get("module_name"),
                "quarto_file": mapping.get("quarto_file"),
            }

    return {"node_to_lean": node_to_lean, "lean_to_node": lean_to_node, "mappings": mappings}


def verify_quarto_files_exist(mappings: List[Dict[str, str]], project_root: Path) -> None:
    """
    Verify that referenced Quarto files actually exist.

    Args:
        mappings: List of mapping dictionaries
        project_root: Root directory of the project
    """
    logger.info("Verifying Quarto file references...")

    for mapping in mappings:
        quarto_file = mapping.get("quarto_file")
        if quarto_file:
            full_path = project_root / quarto_file
            if full_path.exists():
                logger.debug("✓ Found: %s", quarto_file)
            else:
                logger.warning("✗ Missing: %s", quarto_file)


def main() -> None:
    """Main function to extract Lean-Quarto mappings."""
    # Define paths
    project_root = Path(__file__).parent.parent
    lean_dir = project_root / "formal"
    output_file = project_root / "lean_mappings.json"

    logger.info("Starting Lean-Quarto mapping extraction...")

    # Extract mappings
    mappings = extract_all_mappings(lean_dir)
    logger.info("Found %d mappings", len(mappings))

    if mappings:
        # Create bidirectional mapping
        mapping_data = create_bidirectional_mapping(mappings)

        # Verify Quarto files
        verify_quarto_files_exist(mappings, project_root)

        # Save to JSON
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(mapping_data, f, indent=2)
        logger.info("Mappings saved to %s", output_file)

        # Print summary
        logger.info("\nSummary:")
        logger.info("  Total mappings: %d", len(mappings))
        logger.info("  Node to Lean mappings: %d", len(mapping_data["node_to_lean"]))
        logger.info("  Lean to Node mappings: %d", len(mapping_data["lean_to_node"]))
    else:
        logger.warning("No mappings found!")


if __name__ == "__main__":
    main()
