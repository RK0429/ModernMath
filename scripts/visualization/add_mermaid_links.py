#!/usr/bin/env python3
"""
Add click directives to Mermaid diagrams automatically.

This script processes all .qmd files and adds click directives to Mermaid diagram nodes
that reference other mathematical concepts, enabling navigation between pages.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple, Optional, Set
from re import Match

import frontmatter


def extract_node_definitions(mermaid_content: str) -> List[Tuple[str, str, str]]:
    """
    Extract node definitions from Mermaid diagram content.

    Returns a list of tuples: (node_id, display_label, node_type)
    """
    nodes = []

    # Pattern to match node definitions like: def-group["定義: 群"]:::definition
    node_pattern = r'(\S+)\["([^"]+)"\](?::::(\w+))?'

    for match in re.finditer(node_pattern, mermaid_content):
        node_id = match.group(1)
        display_label = match.group(2)
        node_type = match.group(3) or ""

        # Skip special nodes
        if node_id in ["graph", "TD", "LR", "TB", "BT", "RL", "classDef", "class"]:
            continue

        nodes.append((node_id, display_label, node_type))

    return nodes


def extract_existing_clicks(mermaid_content: str) -> Set[str]:
    """
    Extract node IDs that already have click directives.
    """
    click_pattern = r"click\s+(\S+)\s+"
    return {match.group(1) for match in re.finditer(click_pattern, mermaid_content)}


def determine_link_path(node_id: str) -> Optional[str]:
    """
    Determine the relative path for a node ID based on naming conventions.
    """
    # Skip special node IDs
    if node_id.startswith("class ") or node_id in ["graph", "TD", "LR", "TB", "BT", "RL"]:
        return None

    # Standard mathematical concept file patterns
    patterns = ["def-", "thm-", "ex-", "ax-", "prop-", "lem-", "cor-"]

    # Check if node_id matches any standard pattern
    for pattern in patterns:
        if node_id.startswith(pattern):
            return f"{node_id}.html"

    return None


def get_link_tooltip(display_label: str, lang: str = "ja") -> str:
    """
    Generate appropriate tooltip text based on the display label and language.
    """
    # Define label mappings for each language
    ja_mappings = {"定義:": "の定義へ", "定理:": "の定理へ", "例:": "の例へ", "公理:": "の公理へ"}

    en_mappings = {
        "Definition:": " definition",
        "Theorem:": " theorem",
        "Example:": " example",
        "Axiom:": " axiom",
    }

    if lang == "ja":
        for prefix, suffix in ja_mappings.items():
            if prefix in display_label:
                concept = display_label.replace(prefix, "").strip()
                return f"{concept}{suffix}"
        return f"{display_label}へ"

    # English tooltips
    for prefix, suffix in en_mappings.items():
        if prefix in display_label:
            concept = display_label.replace(prefix, "").strip()
            return f"Go to {concept}{suffix}"
    return f"Go to {display_label}"


def add_click_directives(mermaid_content: str, lang: str = "ja") -> str:
    """
    Add click directives to a Mermaid diagram.
    """
    lines = mermaid_content.split("\n")

    # Extract nodes and existing clicks
    nodes = extract_node_definitions(mermaid_content)
    existing_clicks = extract_existing_clicks(mermaid_content)

    # Find where to insert click directives (after the last node or arrow definition)
    insert_index = -1
    for i, line in enumerate(lines):
        stripped = line.strip()
        # Look for node definitions or arrow connections
        has_arrow = "-->" in stripped or "--" in stripped
        has_class_def = ":::" in stripped
        is_node_def = stripped and not stripped.startswith(("click", "%%"))

        if has_arrow or has_class_def or is_node_def:
            insert_index = i

    # Generate click directives
    click_lines = []
    for node_id, display_label, _ in nodes:
        # Skip if already has a click directive
        if node_id in existing_clicks:
            continue

        # Skip the current node (marked with 'current' class)
        if "class " + node_id + " current" in mermaid_content:
            continue

        # Determine the link path
        link_path = determine_link_path(node_id)
        if link_path:
            tooltip = get_link_tooltip(display_label, lang)
            click_lines.append(f'    click {node_id} "{link_path}" "{tooltip}"')

    # Insert click directives if we have any
    if click_lines and insert_index >= 0:
        # Add a blank line before click directives for readability
        if insert_index < len(lines) - 1:
            lines.insert(insert_index + 1, "")
            insert_index += 1

        # Insert all click directives
        for i, click_line in enumerate(click_lines):
            lines.insert(insert_index + 1 + i, click_line)

    return "\n".join(lines)


def process_qmd_file(file_path: Path) -> bool:
    """
    Process a single .qmd file to add click directives to Mermaid diagrams.

    Returns True if the file was modified, False otherwise.
    """
    try:
        # Read the file
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        # Parse frontmatter to get language
        post = frontmatter.loads(content)
        lang = post.get("lang", "en")

        # Find all Mermaid code blocks
        mermaid_pattern = r"```\{mermaid\}(.*?)```"
        modified = False

        def replace_mermaid(match: Match[str]) -> str:
            nonlocal modified
            original_content = match.group(1)
            updated_content = add_click_directives(original_content, lang)

            if original_content != updated_content:
                modified = True

            return f"```{{mermaid}}{updated_content}```"

        # Process all Mermaid blocks
        new_content = re.sub(mermaid_pattern, replace_mermaid, content, flags=re.DOTALL)

        # Write back if modified
        if modified:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(new_content)
            print(f"✅ Updated: {file_path}")
            return True
        print(f"⏭️  Skipped: {file_path} (no changes needed)")
        return False

    except (IOError, ValueError) as e:
        print(f"❌ Error processing {file_path}: {e}")
        return False


def main() -> int:
    """Main function to process all .qmd files."""
    # Get the project root
    script_dir = Path(__file__).parent
    project_root = (
        script_dir.parent.parent
    )  # Go up two levels: visualization -> scripts -> project root
    content_dir = project_root / "content"

    if not content_dir.exists():
        print(f"Error: Content directory not found at {content_dir}")
        sys.exit(1)

    # Find all .qmd files
    qmd_files = list(content_dir.rglob("*.qmd"))

    print(f"Found {len(qmd_files)} .qmd files to process")
    print("=" * 50)

    # Process each file
    modified_count = 0
    for qmd_file in sorted(qmd_files):
        if process_qmd_file(qmd_file):
            modified_count += 1

    print("=" * 50)
    print(f"Summary: Modified {modified_count} out of {len(qmd_files)} files")

    # Always return success - having no changes is not an error
    return 0


if __name__ == "__main__":
    sys.exit(main())
