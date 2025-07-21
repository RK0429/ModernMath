#!/usr/bin/env python3
"""
Validate YAML metadata in all .qmd files to ensure they comply with the schema.
"""

import sys
from typing import List, Dict
from pathlib import Path
import frontmatter


REQUIRED_FIELDS = {"title", "id", "type"}
VALID_TYPES = {
    "Definition",
    "Theorem",
    "Lemma",
    "Proposition",
    "Corollary",
    "Axiom",
    "Example",
}
VALID_STATUS = {"stub", "draft", "complete", "verified"}


def validate_metadata(file_path: Path) -> List[str]:
    """Validate metadata for a single .qmd file."""
    errors = []

    try:
        with open(file_path, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)
            metadata = post.metadata
    except (IOError, OSError, ValueError) as e:
        return [f"Failed to parse frontmatter: {e}"]

    # Check required fields
    missing_fields = REQUIRED_FIELDS - set(metadata.keys())
    if missing_fields:
        errors.append(f"Missing required fields: {', '.join(missing_fields)}")

    # Validate 'type' field
    if "type" in metadata and metadata["type"] not in VALID_TYPES:
        errors.append(
            f"Invalid type '{metadata['type']}'. Must be one of: {', '.join(VALID_TYPES)}"
        )

    # Validate 'status' field if present
    if "status" in metadata and metadata["status"] not in VALID_STATUS:
        errors.append(
            f"Invalid status '{metadata['status']}'. Must be one of: {', '.join(VALID_STATUS)}"
        )

    # Validate 'id' field matches file naming convention
    if "id" in metadata:
        expected_id = file_path.stem
        if metadata["id"] != expected_id:
            errors.append(f"ID '{metadata['id']}' doesn't match filename '{expected_id}'")

    # Validate 'requires' field if present
    if "requires" in metadata:
        if not isinstance(metadata["requires"], list):
            errors.append("'requires' field must be a list")
        else:
            for req in metadata["requires"]:
                if not isinstance(req, str):
                    errors.append(f"Invalid requirement '{req}' - must be a string")

    return errors


def main() -> None:
    """Main validation function."""
    content_dir = Path("content")
    if not content_dir.exists():
        print("Error: content/ directory not found")
        sys.exit(1)

    all_errors: Dict[str, List[str]] = {}
    total_files = 0

    # Find all .qmd files (excluding index.qmd files)
    for qmd_file in content_dir.rglob("*.qmd"):
        # Skip index.qmd files as they are navigation pages, not content nodes
        if qmd_file.name == "index.qmd":
            continue
        total_files += 1
        errors = validate_metadata(qmd_file)
        if errors:
            all_errors[str(qmd_file)] = errors

    # Report results
    if all_errors:
        print(f"❌ Metadata validation failed for {len(all_errors)} out of {total_files} files:\n")
        for file_path, errors in all_errors.items():
            print(f"File: {file_path}")
            for error in errors:
                print(f"  - {error}")
            print()
        sys.exit(1)
    else:
        print(f"✅ All {total_files} .qmd files have valid metadata!")
        sys.exit(0)


if __name__ == "__main__":
    main()
