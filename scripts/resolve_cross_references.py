#!/usr/bin/env python3
"""
Resolve cross-references in Quarto markdown files.

This script converts @-style cross-references (e.g., @def-group) to proper
relative markdown links to eliminate Quarto cross-reference warnings.
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import yaml


def load_node_index(content_dir: Path) -> Dict[str, Path]:
    """
    Build an index of all node IDs to their file paths.

    Args:
        content_dir: Root content directory

    Returns:
        Dictionary mapping node IDs to their file paths
    """
    node_index = {}

    for qmd_file in content_dir.rglob("*.qmd"):
        # Skip index files
        if qmd_file.name == "index.qmd":
            continue

        try:
            # Read YAML front matter
            with open(qmd_file, "r", encoding="utf-8") as f:
                content = f.read()

            # Extract YAML front matter
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


def find_cross_references(content: str) -> List[Tuple[str, str, int, int]]:
    """
    Find all @-style cross-references in content.

    Args:
        content: The markdown content

    Returns:
        List of (reference_id, bracket_text, start_pos, end_pos) tuples
    """
    # Pattern to match @-style references
    # Matches @word-with-hyphens optionally followed by [bracketed text]
    pattern = r"@([a-zA-Z0-9_-]+)(\[[^\]]*\])?"

    references = []
    for match in re.finditer(pattern, content):
        ref_id = match.group(1)
        bracket_text = None
        if match.group(2):
            # Extract text between brackets
            bracket_text = match.group(2)[1:-1]
        references.append((ref_id, bracket_text, match.start(), match.end()))

    return references


def calculate_relative_path(from_file: Path, to_file: Path) -> str:
    """
    Calculate relative path from one file to another.

    Args:
        from_file: Source file path
        to_file: Target file path

    Returns:
        Relative path string
    """
    try:
        # Get the directory of the source file
        from_dir = from_file.parent

        # Calculate relative path from source directory to target file
        # This handles both same-directory and cross-directory references
        rel_path = Path("..") / to_file.parent.name / to_file.name

        # For files in the same directory, simplify the path
        if from_dir == to_file.parent:
            rel_path = Path(to_file.name)

        # Convert to string with forward slashes
        return str(rel_path).replace("\\", "/")

    except ValueError:
        # Fallback: calculate relative path using os.path.relpath
        import os

        rel_path = os.path.relpath(to_file, from_dir)
        return rel_path.replace("\\", "/")


def get_node_title(file_path: Path) -> Optional[str]:
    """
    Extract the title from a node file.

    Args:
        file_path: Path to the .qmd file

    Returns:
        The title or None if not found
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        if content.startswith("---"):
            yaml_end = content.find("---", 3)
            if yaml_end != -1:
                yaml_content = content[3:yaml_end]
                metadata = yaml.safe_load(yaml_content)

                if metadata and "title" in metadata:
                    return metadata["title"]

    except Exception:
        pass

    return None


def pluralize_word(word: str) -> str:
    """
    Simple pluralization for common mathematical terms.

    Args:
        word: The word to pluralize

    Returns:
        Pluralized form
    """
    word_lower = word.lower()

    # Common irregular plurals
    irregular = {
        "matrix": "matrices",
        "vertex": "vertices",
        "basis": "bases",
        "hypothesis": "hypotheses",
        "analysis": "analyses",
    }

    if word_lower in irregular:
        # Preserve original case
        if word[0].isupper():
            return irregular[word_lower].capitalize()
        return irregular[word_lower]

    # Regular pluralization rules
    if word.endswith("y") and len(word) > 1 and word[-2] not in "aeiou":
        return word[:-1] + "ies"
    elif word.endswith(("s", "x", "z", "ch", "sh")):
        return word + "es"
    else:
        return word + "s"


def resolve_references_in_file(
    file_path: Path, node_index: Dict[str, Path], dry_run: bool = False
) -> int:
    """
    Resolve cross-references in a single file.

    Args:
        file_path: Path to the .qmd file to process
        node_index: Dictionary mapping node IDs to file paths
        dry_run: If True, don't write changes, just report them

    Returns:
        Number of references resolved
    """
    with open(file_path, "r", encoding="utf-8") as f:
        original_content = f.read()

    content = original_content
    references = find_cross_references(content)

    if not references:
        return 0

    # Process references in reverse order to maintain positions
    resolved_count = 0
    for ref_id, bracket_text, start, end in reversed(references):
        if ref_id in node_index:
            target_file = node_index[ref_id]

            # Skip if it's a self-reference
            if target_file == file_path:
                continue

            # Calculate relative path
            rel_path = calculate_relative_path(file_path, target_file)

            # Determine link text
            link_text = None

            # First check if there's meaningful bracketed text
            if bracket_text and len(bracket_text.strip()) > 2:
                # Use bracketed text if it's meaningful (more than 2 characters)
                link_text = bracket_text.strip()
            else:
                # Otherwise, get the title from the target file
                title = get_node_title(target_file)
                if title:
                    # Clean the title (remove "Definition:", "Theorem:", etc. prefix if present)
                    if ":" in title:
                        clean_title = title.split(":", 1)[1].strip()
                    else:
                        clean_title = title

                    # If bracketed text is 's' or 'es', pluralize the title
                    if bracket_text and bracket_text.strip() in ["s", "es"]:
                        link_text = pluralize_word(clean_title)
                    else:
                        link_text = clean_title
                else:
                    # Fallback to the ID
                    link_text = ref_id.replace("-", " ").title()

            # Create the markdown link
            link = f"[{link_text}]({rel_path})"

            # Replace the reference
            content = content[:start] + link + content[end:]
            resolved_count += 1

            if not dry_run:
                bracket_part = f"[{bracket_text}]" if bracket_text else ""
                print(f"  Resolved: @{ref_id}{bracket_part} -> {link}")

    if content != original_content and not dry_run:
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(content)

    return resolved_count


def main():
    parser = argparse.ArgumentParser(
        description="Resolve cross-references in Quarto markdown files"
    )
    parser.add_argument(
        "--content-dir",
        type=Path,
        default=Path("content"),
        help="Content directory (default: content)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be changed without modifying files",
    )
    parser.add_argument("--file", type=Path, help="Process only a specific file")

    args = parser.parse_args()

    # Make content_dir absolute
    content_dir = args.content_dir.resolve()

    if not content_dir.exists():
        print(f"Error: Content directory '{content_dir}' does not exist", file=sys.stderr)
        sys.exit(1)

    print(f"Building node index from {content_dir}...")
    node_index = load_node_index(content_dir)
    print(f"Found {len(node_index)} nodes in the knowledge graph")

    if args.dry_run:
        print("\n--- DRY RUN MODE ---")

    # Process files
    total_resolved = 0
    files_processed = 0

    if args.file:
        # Process single file
        files_to_process = [args.file.resolve()]
    else:
        # Process all .qmd files
        files_to_process = list(content_dir.rglob("*.qmd"))

    for qmd_file in files_to_process:
        # Skip index files
        if qmd_file.name == "index.qmd":
            continue

        print(f"\nProcessing: {qmd_file.relative_to(content_dir.parent)}")
        resolved = resolve_references_in_file(qmd_file, node_index, args.dry_run)

        if resolved > 0:
            total_resolved += resolved
            files_processed += 1
            print(f"  Resolved {resolved} cross-references")
        else:
            print("  No cross-references to resolve")

    action = "Would resolve" if args.dry_run else "Resolved"
    print(f"\n{action} {total_resolved} cross-references in {files_processed} files")

    if args.dry_run:
        print("\nRun without --dry-run to apply changes")


if __name__ == "__main__":
    main()
