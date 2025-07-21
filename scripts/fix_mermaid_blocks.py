#!/usr/bin/env python3
"""
Fix Mermaid diagram blocks in .qmd files.

This script corrects the syntax of Mermaid diagrams to use proper Quarto code blocks.
"""

import re
from pathlib import Path
from typing import List, Match


def fix_mermaid_block(content: str) -> str:
    """Fix Mermaid diagram blocks in the content."""
    # Pattern to match incorrectly formatted Mermaid blocks
    # This matches the entire block from %%| to the closing ```
    pattern = r"(%%\|[^\n]*\n)(graph\s+[A-Z]+.*?)(\n```)(.*?click.*?```)?"

    # Replace with properly formatted Mermaid block
    def replacement(match: Match[str]) -> str:
        options = match.group(1)  # Keep the %%| line as is
        diagram_content = match.group(2).rstrip()  # The graph definition
        closing = match.group(3)  # The closing ```
        click_section = match.group(4) or ""  # Optional click directives section

        # Build the proper Mermaid block
        return f"```{{mermaid}}\n{options}{diagram_content}{closing}{click_section}"

    # Apply the fix
    fixed_content = re.sub(pattern, replacement, content, flags=re.DOTALL | re.MULTILINE)

    return fixed_content


def process_file(file_path: Path) -> bool:
    """Process a single .qmd file."""
    try:
        content = file_path.read_text(encoding="utf-8")
        original_content = content

        # Fix Mermaid blocks
        fixed_content = fix_mermaid_block(content)

        # Only write if changes were made
        if fixed_content != original_content:
            file_path.write_text(fixed_content, encoding="utf-8")
            print(f"Fixed: {file_path}")
            return True

        print(f"No changes needed: {file_path}")
        return False

    except (OSError, UnicodeDecodeError) as e:
        print(f"Error processing {file_path}: {e}")
        return False


def main() -> None:
    """Main function to process all .qmd files."""
    # Get the project root
    script_dir = Path(__file__).parent
    project_root = script_dir.parent
    content_dir = project_root / "content"

    # Find all .qmd files
    qmd_files: List[Path] = list(content_dir.rglob("*.qmd"))

    print(f"Found {len(qmd_files)} .qmd files to process")

    # Process each file
    fixed_count = 0
    for qmd_file in qmd_files:
        if process_file(qmd_file):
            fixed_count += 1

    print(f"\nSummary: Fixed {fixed_count} files out of {len(qmd_files)} total files")


if __name__ == "__main__":
    main()
