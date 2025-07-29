#!/usr/bin/env python3
"""
Fix empty Mermaid blocks that cause trust errors in the rendered site.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple


def find_empty_mermaid_blocks(content: str) -> List[Tuple[int, int]]:
    """Find positions of empty Mermaid blocks in content."""
    lines = content.split("\n")
    empty_blocks = []

    i = 0
    while i < len(lines):
        # Check for Mermaid block start
        if lines[i].strip() == "```{mermaid}":
            # Check if next line is the closing ```
            if i + 1 < len(lines) and lines[i + 1].strip() == "```":
                empty_blocks.append((i, i + 1))
                i += 2
            else:
                i += 1
        else:
            i += 1

    return empty_blocks


def remove_empty_mermaid_blocks(content: str) -> Tuple[str, int]:
    """Remove empty Mermaid blocks from content."""
    lines = content.split("\n")
    empty_blocks = find_empty_mermaid_blocks(content)

    if not empty_blocks:
        return content, 0

    # Remove blocks in reverse order to maintain line indices
    for start, end in reversed(empty_blocks):
        # Remove the empty block and any surrounding blank lines
        # Check for blank lines before
        while start > 0 and lines[start - 1].strip() == "":
            start -= 1

        # Check for blank lines after
        while end < len(lines) - 1 and lines[end + 1].strip() == "":
            end += 1

        # Remove the lines
        del lines[start : end + 1]

    # Reconstruct content
    fixed_content = "\n".join(lines)

    # Clean up multiple consecutive newlines
    fixed_content = re.sub(r"\n{3,}", "\n\n", fixed_content)

    return fixed_content, len(empty_blocks)


def process_file(file_path: Path) -> bool:
    """Process a single file to remove empty Mermaid blocks."""
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    fixed_content, num_removed = remove_empty_mermaid_blocks(content)

    if num_removed > 0:
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(fixed_content)
        return True

    return False


def main() -> int:
    """Main function to fix empty Mermaid blocks in all content files."""
    content_dir = Path("content")

    fixed_files = []
    total_blocks_removed = 0

    # Process all .qmd files
    for qmd_file in content_dir.rglob("*.qmd"):
        with open(qmd_file, "r", encoding="utf-8") as f:
            content = f.read()

        # Check for empty blocks
        empty_blocks = find_empty_mermaid_blocks(content)
        if empty_blocks:
            if process_file(qmd_file):
                fixed_files.append(qmd_file)
                total_blocks_removed += len(empty_blocks)

    # Report results
    if fixed_files:
        print(f"✅ Fixed {total_blocks_removed} empty Mermaid blocks in {len(fixed_files)} files:")
        for file_path in fixed_files:
            print(f"   - {file_path}")
    else:
        print("✅ No empty Mermaid blocks found in any files.")

    return len(fixed_files)


if __name__ == "__main__":
    sys.exit(0 if main() == 0 else 1)
