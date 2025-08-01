#!/usr/bin/env python3
"""
Fix placement of Interactive Visualization sections to ensure they always appear at the end of
articles.
"""

import argparse
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import frontmatter


def identify_sections(content: str) -> List[Dict[str, Any]]:
    """Identify all sections in the content with their positions and types."""
    sections = []

    # Pattern to match section headers (## or ###)
    section_pattern = r"^(#{2,3})\s+(.+)$"

    lines = content.split("\n")
    current_pos = 0

    for i, line in enumerate(lines):
        match = re.match(section_pattern, line)
        if match:
            level = match.group(1)
            title = match.group(2)

            # Determine section type
            section_type = "content"
            if any(
                keyword in title
                for keyword in ["Interactive Visualization", "インタラクティブ可視化"]
            ):
                section_type = "interactive"

            sections.append(
                {
                    "line_num": i,
                    "level": level,
                    "title": title,
                    "type": section_type,
                    "start_pos": current_pos,
                }
            )

        current_pos += len(line) + 1  # +1 for newline

    # Add end positions
    for i, section in enumerate(sections):
        if i < len(sections) - 1:
            section["end_pos"] = int(sections[i + 1]["start_pos"]) - 1
        else:
            section["end_pos"] = len(content)

    return sections


def extract_visualization_section(
    content: str, sections: List[Dict[str, Any]]
) -> Tuple[str, Optional[str]]:
    """Extract interactive visualization section and return cleaned content and extracted
    section."""
    visualization_section = None
    section_to_remove = None

    # Identify visualization section to extract
    for section in sections:
        if section["type"] == "interactive":
            section_to_remove = section
            break

    if not section_to_remove:
        return content, None

    # Extract section content
    section_content = content[
        section_to_remove["start_pos"] : section_to_remove["end_pos"]
    ].rstrip()
    visualization_section = section_content

    # Remove the section from content
    before = content[: section_to_remove["start_pos"]].rstrip()
    after = content[section_to_remove["end_pos"] :].lstrip()
    cleaned_content = before + "\n\n" + after if after else before

    # Clean up multiple consecutive newlines
    cleaned_content = re.sub(r"\n{3,}", "\n\n", cleaned_content)
    cleaned_content = cleaned_content.rstrip()

    return cleaned_content, visualization_section


def fix_visualization_placement(content: str) -> str:
    """Fix the placement of interactive visualization section to ensure it's at the end."""
    sections = identify_sections(content)

    # Check if visualization section exists
    viz_sections = [s for s in sections if s["type"] == "interactive"]
    if not viz_sections:
        return content

    # Check if interactive visualization is already at the end
    content_sections = [s for s in sections if s["type"] == "content"]
    if content_sections and viz_sections:
        last_content_pos = max(s["line_num"] for s in content_sections)
        viz_pos = viz_sections[0]["line_num"]

        if viz_pos > last_content_pos:
            # Already correctly placed
            return content

    # Extract visualization section
    cleaned_content, viz_content = extract_visualization_section(content, sections)

    # Append visualization section at the end
    if viz_content:
        result = cleaned_content + "\n\n" + viz_content
        return result

    return content


def process_file(qmd_file: Path) -> Optional[str]:
    """Process a single .qmd file to fix visualization placement."""
    try:
        with open(qmd_file, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)

        original_content = post.content
        new_content = fix_visualization_placement(original_content)

        # Check if content changed
        if new_content != original_content:
            post.content = new_content
            with open(qmd_file, "w", encoding="utf-8") as f:
                f.write(frontmatter.dumps(post))
            return "updated"

        return "unchanged"

    except (OSError, UnicodeDecodeError, ValueError) as e:
        print(f"Error processing {qmd_file}: {e}")
        return "error"


def check_misplaced_sections(content_dir: Path) -> None:
    """Check for files with misplaced visualization sections."""
    misplaced_files = []

    for qmd_file in content_dir.rglob("*.qmd"):
        try:
            with open(qmd_file, "r", encoding="utf-8") as f:
                post = frontmatter.load(f)

            sections = identify_sections(post.content)
            content_sections = [s for s in sections if s["type"] == "content"]
            viz_sections = [s for s in sections if s["type"] == "interactive"]

            if content_sections and viz_sections:
                last_content_pos = max(s["line_num"] for s in content_sections)
                first_viz_pos = min(s["line_num"] for s in viz_sections)

                if first_viz_pos < last_content_pos:
                    misplaced_files.append(qmd_file)

        except (OSError, UnicodeDecodeError, ValueError):
            continue

    if misplaced_files:
        print(f"Found {len(misplaced_files)} files with misplaced visualization sections:")
        for file_path in misplaced_files:
            print(f"  - {file_path}")
    else:
        print("✅ All files have correctly placed interactive visualization sections")


def main() -> None:
    """Main function to fix visualization placement in all content files."""
    parser = argparse.ArgumentParser(description="Fix interactive visualization section placement")
    parser.add_argument(
        "--check", action="store_true", help="Check for misplaced sections without fixing"
    )
    args = parser.parse_args()

    content_dir = Path("content")

    if args.check:
        check_misplaced_sections(content_dir)
        return

    # Fix mode
    updated_files = []
    unchanged_files = []
    error_files = []

    for qmd_file in content_dir.rglob("*.qmd"):
        result = process_file(qmd_file)

        if result == "updated":
            updated_files.append(qmd_file)
        elif result == "unchanged":
            unchanged_files.append(qmd_file)
        elif result == "error":
            error_files.append(qmd_file)

    # Report results
    if updated_files:
        print(f"✅ Fixed visualization placement in {len(updated_files)} files")

    if unchanged_files:
        print(f"⏭️  {len(unchanged_files)} files already have correct placement")

    if error_files:
        print(f"❌ {len(error_files)} files had errors")

    print(
        f"\n📊 Total: {len(updated_files)} updated, {len(unchanged_files)} unchanged, "
        f"{len(error_files)} errors"
    )


if __name__ == "__main__":
    main()
