#!/usr/bin/env python3
"""
Fix placement of visualization sections (Dependency Graph and Interactive Visualization)
to ensure they always appear at the end of articles.
"""

import argparse
import re
from pathlib import Path
from typing import Tuple, List, Dict, Optional, Any
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
                for keyword in [
                    "Dependency Graph",
                    "依存グラフ",
                    "Local Graph",
                    "局所依存関係グラフ",
                ]
            ):
                section_type = "dependency"
            elif any(
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


def extract_visualization_sections(
    content: str, sections: List[Dict[str, Any]]
) -> Tuple[str, List[str]]:
    """Extract visualization sections and return cleaned content and extracted sections."""
    visualization_sections = []
    sections_to_remove = []

    # Identify visualization sections to extract
    for section in sections:
        if section["type"] in ["dependency", "interactive"]:
            sections_to_remove.append(section)

    # Sort sections to remove by position (reverse order for removal)
    def get_start_pos(section: Dict[str, Any]) -> int:
        return int(section["start_pos"])

    sections_to_remove.sort(key=get_start_pos, reverse=True)

    # Extract sections and remove from content
    cleaned_content = content
    for section in sections_to_remove:
        section_content = content[section["start_pos"] : section["end_pos"]].rstrip()
        visualization_sections.append((section["type"], section_content))

        # Remove the section from content
        before = cleaned_content[: section["start_pos"]].rstrip()
        after = cleaned_content[section["end_pos"] :].lstrip()
        cleaned_content = before + "\n\n" + after if after else before

    # Clean up multiple consecutive newlines
    cleaned_content = re.sub(r"\n{3,}", "\n\n", cleaned_content)
    cleaned_content = cleaned_content.rstrip()

    # Sort visualization sections: dependency first, then interactive
    def sort_key(x: Tuple[str, str]) -> int:
        return 0 if x[0] == "dependency" else 1

    visualization_sections.sort(key=sort_key)

    return cleaned_content, [content for _, content in visualization_sections]


def fix_visualization_placement(content: str) -> str:
    """Fix the placement of visualization sections to ensure they're at the end."""
    sections = identify_sections(content)

    # Check if visualization sections are already at the end
    content_sections = [s for s in sections if s["type"] == "content"]
    viz_sections = [s for s in sections if s["type"] in ["dependency", "interactive"]]

    if not viz_sections:
        return content

    # Check if all viz sections are after all content sections
    if content_sections and viz_sections:
        last_content_pos = max(s["line_num"] for s in content_sections)
        first_viz_pos = min(s["line_num"] for s in viz_sections)

        if first_viz_pos > last_content_pos:
            # Already correctly placed
            return content

    # Extract visualization sections
    cleaned_content, viz_contents = extract_visualization_sections(content, sections)

    # Append visualization sections at the end
    if viz_contents:
        result = cleaned_content
        for viz_content in viz_contents:
            result += "\n\n" + viz_content
        return result

    return content


def update_visualization_content(
    content: str, node_id: str, diagram_content: Optional[str], is_japanese: bool
) -> str:
    """Update or add visualization sections with new content."""
    sections = identify_sections(content)

    # Extract existing visualization sections
    cleaned_content, _ = extract_visualization_sections(content, sections)

    # Create new visualization sections
    sections_to_add = []

    if diagram_content:
        if is_japanese:
            dependency_section = f"## 依存グラフ\n\n{diagram_content}"
        else:
            dependency_section = f"## Dependency Graph\n\n{diagram_content}"
        sections_to_add.append(dependency_section)

    # Always add interactive visualization
    if is_japanese:
        interactive_section = f"""## インタラクティブ可視化

ローカル知識グラフの近傍をインタラクティブに探索：

::: {{.graph-viz data-id="{node_id}" data-width="700" data-height="500"}}
:::

次のことができます：
- ノードを**ドラッグ**してレイアウトを再配置
- マウスホイールで**ズーム**イン/アウト
- ノードに**ホバー**して詳細を表示
- [別ウィンドウ](../../output/interactive/{node_id}.html){{target="_blank"}}で完全なインタラクティブ版を表示"""
    else:
        interactive_section = f"""## Interactive Visualization

Explore the local knowledge graph neighborhood interactively:

::: {{.graph-viz data-id="{node_id}" data-width="700" data-height="500"}}
:::

You can:
- **Drag** nodes to rearrange the layout
- **Zoom** in/out with your mouse wheel
- **Hover** over nodes to see details
- View the [full interactive version](../../output/interactive/{node_id}.html){{target="_blank"}}"""

    sections_to_add.append(interactive_section)

    # Combine cleaned content with new visualization sections
    result = cleaned_content
    for section in sections_to_add:
        result += "\n\n" + section

    return result


def process_file(qmd_file: Path, fix_only: bool = False) -> Optional[str]:
    """Process a single .qmd file to fix visualization placement."""
    with open(qmd_file, "r", encoding="utf-8") as f:
        post = frontmatter.load(f)

    original_content = post.content

    if fix_only:
        # Just fix the placement without updating content
        new_content = fix_visualization_placement(original_content)
    else:
        # Full update with new diagram content
        if "id" not in post.metadata:
            return None

        node_id = post.metadata["id"]
        diagrams_dir = Path("output/mermaid")
        diagram_file = diagrams_dir / f"{node_id}.mermaid"

        # Determine language from path
        is_japanese = "/ja/" in str(qmd_file)

        # Read diagram content if available
        diagram_content = None
        if diagram_file.exists():
            with open(diagram_file, "r", encoding="utf-8") as f:
                diagram_content = f.read()

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


def check_misplaced_sections(content_dir: Path) -> None:
    """Check for files with misplaced visualization sections."""
    misplaced_files = []

    for qmd_file in content_dir.rglob("*.qmd"):
        with open(qmd_file, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)

        sections = identify_sections(post.content)
        content_sections = [s for s in sections if s["type"] == "content"]
        viz_sections = [s for s in sections if s["type"] in ["dependency", "interactive"]]

        if content_sections and viz_sections:
            last_content_pos = max(s["line_num"] for s in content_sections)
            first_viz_pos = min(s["line_num"] for s in viz_sections)

            if first_viz_pos < last_content_pos:
                misplaced_files.append(qmd_file)

    if misplaced_files:
        print(f"Found {len(misplaced_files)} files with misplaced visualization sections:")
        for file_path in misplaced_files:
            print(f"  - {file_path}")
    else:
        print("✅ All files have correctly placed visualization sections")


def main() -> None:
    """Main function to fix visualization placement in all content files."""
    parser = argparse.ArgumentParser(description="Fix visualization section placement")
    parser.add_argument(
        "--fix-only", action="store_true", help="Only fix placement without updating content"
    )
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

    for qmd_file in content_dir.rglob("*.qmd"):
        result = process_file(qmd_file, fix_only=args.fix_only)

        if result == "updated":
            updated_files.append(qmd_file)
        elif result == "unchanged":
            unchanged_files.append(qmd_file)

    # Report results
    if updated_files:
        print(f"✅ Fixed visualization placement in {len(updated_files)} files:")
        for file_path in updated_files:
            print(f"   - {file_path}")

    if unchanged_files:
        print(f"\n⏭️  {len(unchanged_files)} files already have correct placement")

    print(f"\n📊 Total: {len(updated_files)} updated, {len(unchanged_files)} unchanged")


if __name__ == "__main__":
    main()
