#!/usr/bin/env python3
"""
Insert generated Mermaid diagrams into Quarto content files with proper placement.
This script ensures visualization sections are always at the end of articles.
"""

from pathlib import Path
from typing import Optional
import frontmatter

from fix_visualization_placement import update_visualization_content


def process_file(qmd_file: Path, diagrams_dir: Path) -> Optional[str]:
    """Process a single .qmd file using the new placement logic."""
    with open(qmd_file, "r", encoding="utf-8") as f:
        post = frontmatter.load(f)

    if "id" not in post.metadata:
        return None

    node_id = post.metadata["id"]

    # Determine language from path
    is_japanese = "/ja/" in str(qmd_file)
    lang = "ja" if is_japanese else "en"

    # Get language-specific diagram file
    diagram_file = diagrams_dir / lang / f"{node_id}.mermaid"

    # Read diagram content if available
    diagram_content = None
    if diagram_file.exists():
        with open(diagram_file, "r", encoding="utf-8") as f:
            diagram_content = f.read()
    else:
        # No diagram file, skip this file
        return None

    # Use the new update function that ensures proper placement
    original_content = post.content
    new_content = update_visualization_content(
        original_content, node_id, diagram_content, is_japanese
    )

    # Check if content changed
    if new_content != original_content:
        post.content = new_content
        with open(qmd_file, "w", encoding="utf-8") as f:
            f.write(frontmatter.dumps(post))
        return "updated"

    return "unchanged"


def insert_diagrams() -> None:
    """Insert Mermaid diagrams and interactive visualizations into Quarto content files."""
    content_dir = Path("content")
    diagrams_dir = Path("output/mermaid")

    if not diagrams_dir.exists():
        print("Error: No diagrams found in output/mermaid/")
        print("Run generate_mermaid.py first.")
        return

    updated_files = []
    unchanged_files = []

    # Process each .qmd file
    for qmd_file in content_dir.rglob("*.qmd"):
        result = process_file(qmd_file, diagrams_dir)

        if result == "updated":
            updated_files.append(qmd_file)
        elif result == "unchanged":
            unchanged_files.append(qmd_file)

    # Report results
    if updated_files:
        print(
            f"✅ Updated {len(updated_files)} files with "
            "Mermaid diagrams and interactive visualizations:"
        )
        for file_path in updated_files:
            print(f"   - {file_path}")

    if unchanged_files:
        print(f"\n⏭️  {len(unchanged_files)} files already have visualization sections")

    print(f"\n📊 Total: {len(updated_files)} updated, {len(unchanged_files)} unchanged")


def main() -> None:
    """Main function."""
    insert_diagrams()


if __name__ == "__main__":
    main()
