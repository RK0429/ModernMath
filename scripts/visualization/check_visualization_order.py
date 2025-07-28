#!/usr/bin/env python3
"""Check for .qmd files where visualization sections are not at the end."""

import re
from pathlib import Path
from typing import List, Tuple, Optional


def extract_sections(content: str) -> List[Tuple[str, int]]:
    """Extract all section headers and their positions from content."""
    sections = []

    # Match both ## and ### headers
    header_pattern = re.compile(r"^(#{2,3})\s+(.+)$", re.MULTILINE)

    for match in header_pattern.finditer(content):
        title = match.group(2).strip()
        position = match.start()
        sections.append((title, position))

    return sections


def check_visualization_order(file_path: Path) -> Optional[str]:
    """Check if visualization sections appear before other content sections."""

    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()
    except IOError:
        return None

    sections = extract_sections(content)
    if not sections:
        return None

    # Visualization section titles in both languages
    viz_titles = {
        "Dependency Graph",
        "依存関係グラフ",
        "Interactive Visualization",
        "インタラクティブ可視化",
    }

    # Content section titles that should come before visualizations
    content_titles = {
        "Examples",
        "例",
        "Properties",
        "性質",
        "特性",
        "Related",
        "関連",
        "Consequences",
        "結果",
        "Applications",
        "応用",
        "Notes",
        "注記",
        "Remarks",
        "備考",
        "Proof",
        "証明",
        "See Also",
        "関連項目",
        "Further Reading",
        "参考文献",
    }

    # Find positions of visualization sections
    viz_positions = []
    for title, pos in sections:
        if any(viz in title for viz in viz_titles):
            viz_positions.append((title, pos))

    if not viz_positions:
        return None

    # Find positions of content sections
    content_positions = []
    for title, pos in sections:
        if any(content in title for content in content_titles):
            content_positions.append((title, pos))

    if not content_positions:
        return None

    # Check if any visualization section appears before any content section
    earliest_viz_pos = min(pos for _, pos in viz_positions)
    latest_content_pos = max(pos for _, pos in content_positions)

    if earliest_viz_pos < latest_content_pos:
        # Find which sections are out of order
        viz_before = [title for title, pos in viz_positions if pos < latest_content_pos]
        content_after = [title for title, pos in content_positions if pos > earliest_viz_pos]

        return f"Visualization sections {viz_before} appear before content sections {content_after}"

    return None


def main() -> None:
    """Find all .qmd files with visualization sections not at the end."""

    # Get the project root relative to this script
    script_path = Path(__file__).resolve()
    project_root = script_path.parent.parent.parent
    content_dir = project_root / "content"

    if not content_dir.exists():
        print(f"Content directory not found: {content_dir}")
        return

    files_with_issues = []

    # Find all .qmd files
    for qmd_file in content_dir.rglob("*.qmd"):
        # Skip index files
        if qmd_file.name == "index.qmd":
            continue

        issue = check_visualization_order(qmd_file)
        if issue:
            relative_path = qmd_file.relative_to(content_dir)
            files_with_issues.append((relative_path, issue))

    if files_with_issues:
        print(f"Found {len(files_with_issues)} files with visualization sections not at the end:\n")

        for file_path, issue in sorted(files_with_issues):
            print(f"{file_path}:")
            print(f"  {issue}\n")
    else:
        print("All files have visualization sections at the end (or no visualization sections).")


if __name__ == "__main__":
    main()
