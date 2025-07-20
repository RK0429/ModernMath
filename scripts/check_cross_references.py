#!/usr/bin/env python3
"""
Check for potential cross-reference warnings in Quarto files.
This script validates cross-references without needing to run full quarto render.
"""

import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple
import yaml
import argparse


def load_node_index(content_dir: Path) -> Dict[str, Path]:
    """Build an index of all node IDs to their file paths."""
    node_index = {}

    for qmd_file in content_dir.rglob("*.qmd"):
        if qmd_file.name == "index.qmd":
            continue

        try:
            with open(qmd_file, "r", encoding="utf-8") as f:
                content = f.read()

            if content.startswith("---"):
                yaml_end = content.find("---", 3)
                if yaml_end != -1:
                    yaml_content = content[3:yaml_end]
                    metadata = yaml.safe_load(yaml_content)

                    if metadata and "id" in metadata:
                        node_id = metadata["id"]
                        node_index[node_id] = qmd_file

        except Exception as e:
            print(f"Warning: Error reading {qmd_file}: {e}", file=sys.stderr)

    return node_index


def find_markdown_links(content: str) -> List[Tuple[str, str, int]]:
    """Find all markdown links in content."""
    # Pattern to match markdown links: [text](path)
    pattern = r"\[([^\]]+)\]\(([^)]+)\)"

    links = []
    for match in re.finditer(pattern, content):
        link_text = match.group(1)
        link_path = match.group(2)
        position = match.start()

        # Skip external links and anchors
        if link_path.startswith(("http://", "https://", "#", "mailto:")):
            continue

        links.append((link_text, link_path, position))

    return links


def validate_link(from_file: Path, link_path: str) -> Tuple[bool, str]:
    """
    Validate if a link path is correct.

    Returns:
        (is_valid, error_message)
    """
    # Convert link path to absolute path from the source file
    from_dir = from_file.parent

    try:
        # Resolve the path
        if link_path.startswith("../"):
            # Cross-directory reference
            target_path = (from_dir / link_path).resolve()
        else:
            # Same directory reference
            target_path = (from_dir / link_path).resolve()

        # Check if the file exists
        if not target_path.exists():
            return False, f"File not found: {link_path}"

        # Check if the path is within the content directory
        content_root = from_file.parent.parent
        try:
            target_path.relative_to(content_root)
        except ValueError:
            return False, f"Path outside content directory: {link_path}"

        return True, ""

    except Exception as e:
        return False, f"Invalid path: {link_path} ({str(e)})"


def check_file(file_path: Path, node_index: Dict[str, Path]) -> List[str]:
    """Check a single file for cross-reference issues."""
    warnings = []

    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    # Find all markdown links
    links = find_markdown_links(content)

    for link_text, link_path, position in links:
        # Skip if it's not a .qmd file
        if not link_path.endswith(".qmd"):
            continue

        # Validate the link
        is_valid, error_msg = validate_link(file_path, link_path)

        if not is_valid:
            # Find line number
            line_num = content[:position].count("\n") + 1
            warnings.append(f"  Line {line_num}: {error_msg}")

    return warnings


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Check for cross-reference warnings in Quarto files"
    )
    parser.add_argument(
        "--content-dir",
        type=Path,
        default=Path("content"),
        help="Content directory (default: content)",
    )
    parser.add_argument("--file", type=Path, help="Check only a specific file")
    parser.add_argument(
        "--verbose", action="store_true", help="Show all files checked, even without warnings"
    )

    args = parser.parse_args()

    content_dir = args.content_dir.resolve()

    if not content_dir.exists():
        print(f"Error: Content directory '{content_dir}' does not exist", file=sys.stderr)
        sys.exit(1)

    print("Building node index...")
    node_index = load_node_index(content_dir)
    print(f"Found {len(node_index)} nodes\n")

    total_warnings = 0
    files_with_warnings = 0

    if args.file:
        files_to_check = [args.file.resolve()]
    else:
        files_to_check = list(content_dir.rglob("*.qmd"))

    for qmd_file in files_to_check:
        if qmd_file.name == "index.qmd":
            continue

        warnings = check_file(qmd_file, node_index)

        if warnings:
            print(f"WARN: {qmd_file.relative_to(content_dir.parent)}")
            for warning in warnings:
                print(warning)
            print()
            total_warnings += len(warnings)
            files_with_warnings += 1
        elif args.verbose:
            print(f"OK: {qmd_file.relative_to(content_dir.parent)}")

    if total_warnings > 0:
        print(f"\nFound {total_warnings} warnings in {files_with_warnings} files")
        sys.exit(1)
    else:
        print("No cross-reference warnings found!")


if __name__ == "__main__":
    main()
