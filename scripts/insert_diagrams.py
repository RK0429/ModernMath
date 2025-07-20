#!/usr/bin/env python3
"""
Insert generated Mermaid diagrams into Quarto content files.
"""

from pathlib import Path
from typing import Tuple, Optional, Any, List
import frontmatter


def check_existing_content(post: Any) -> Tuple[bool, bool]:
    """Check what visualization content already exists in the post."""
    has_mermaid_diagram = (
        "## Dependency Graph" in post.content
        or "## Local Graph" in post.content
        or "## 依存関係グラフ" in post.content
        or "## 局所依存関係グラフ" in post.content
        or "```{mermaid}" in post.content
    )

    has_interactive = (
        "## Interactive Visualization" in post.content
        or "## インタラクティブ可視化" in post.content
        or ".graph-viz" in post.content
    )

    return has_mermaid_diagram, has_interactive


def create_content_sections(
    node_id: str, diagram_content: str, is_japanese: bool
) -> Tuple[str, str]:
    """Create the dependency and interactive sections based on language."""
    if is_japanese:
        dependency_section = f"\n\n## 依存グラフ\n\n{diagram_content}"
        interactive_section = f"""

## インタラクティブ可視化

ローカル知識グラフの近傍をインタラクティブに探索：

::: {{.graph-viz data-id="{node_id}" data-width="700" data-height="500"}}
:::

次のことができます：
- ノードを**ドラッグ**してレイアウトを再配置
- マウスホイールで**ズーム**イン/アウト
- ノードに**ホバー**して詳細を表示
- [別ウィンドウ](../../output/interactive/{node_id}.html){{target="_blank"}}で完全なインタラクティブ版を表示"""
    else:
        dependency_section = f"\n\n## Dependency Graph\n\n{diagram_content}"
        interactive_section = f"""

## Interactive Visualization

Explore the local knowledge graph neighborhood interactively:

::: {{.graph-viz data-id="{node_id}" data-width="700" data-height="500"}}
:::

You can:
- **Drag** nodes to rearrange the layout
- **Zoom** in/out with your mouse wheel
- **Hover** over nodes to see details
- View the [full interactive version](../../output/interactive/{node_id}.html){{target="_blank"}}
  in a new window
"""

    return dependency_section, interactive_section


def insert_content_before_references(post: Any, sections: List[str]) -> str:
    """Insert content before References section if it exists."""
    if "## References" in post.content:
        parts = post.content.split("## References")
        return str(parts[0].rstrip() + "".join(sections) + "\n\n## References" + parts[1])

    return str(post.content.rstrip() + "".join(sections))


def find_insertion_point(post: Any) -> Optional[int]:
    """Find where to insert interactive section after existing diagram."""
    headers = ["## References", "## Related", "## See Also", "## 関連", "## 参照"]
    for header in headers:
        if header in post.content:
            return int(post.content.find(header))
    return None


def process_file(qmd_file: Path, diagrams_dir: Path) -> Optional[str]:
    """Process a single .qmd file."""
    with open(qmd_file, "r", encoding="utf-8") as f:
        post = frontmatter.load(f)

    if "id" not in post.metadata:
        return None

    node_id = post.metadata["id"]
    diagram_file = diagrams_dir / f"{node_id}.mermaid"

    if not diagram_file.exists():
        return None

    # Determine language from path
    is_japanese = "/ja/" in str(qmd_file)

    # Check what's already present
    has_mermaid, has_interactive = check_existing_content(post)

    # Skip if both already present
    if has_mermaid and has_interactive:
        return "skipped"

    # Read diagram content
    with open(diagram_file, "r", encoding="utf-8") as f:
        diagram_content = f.read()

    # Create the content sections
    dependency_section, interactive_section = create_content_sections(
        node_id, diagram_content, is_japanese
    )

    # Handle different cases
    if not has_mermaid and not has_interactive:
        # Add both sections
        new_content = insert_content_before_references(
            post, [dependency_section, interactive_section]
        )
        result = "updated"

    elif has_mermaid and not has_interactive:
        # Only add interactive section after the existing diagram
        insert_point = find_insertion_point(post)

        if insert_point is None:
            new_content = post.content.rstrip() + interactive_section
        else:
            new_content = (
                post.content[:insert_point].rstrip()
                + interactive_section
                + "\n\n"
                + post.content[insert_point:]
            )
        result = "added_interactive"
    else:
        return None

    # Write back
    post.content = new_content
    with open(qmd_file, "w", encoding="utf-8") as f:
        f.write(frontmatter.dumps(post))

    return result


def insert_diagrams() -> None:
    """Insert Mermaid diagrams and interactive visualizations into Quarto content files."""
    content_dir = Path("content")
    diagrams_dir = Path("output/mermaid")

    if not diagrams_dir.exists():
        print("Error: No diagrams found in output/mermaid/")
        print("Run generate_mermaid.py first.")
        return

    updated_files = []
    skipped_files = []
    added_interactive = []

    # Process each .qmd file
    for qmd_file in content_dir.rglob("*.qmd"):
        result = process_file(qmd_file, diagrams_dir)

        if result == "updated":
            updated_files.append(qmd_file)
        elif result == "added_interactive":
            added_interactive.append(qmd_file)
        elif result == "skipped":
            skipped_files.append(qmd_file)

    # Report results
    if updated_files:
        print(
            f"✅ Updated {len(updated_files)} files with "
            "Mermaid diagrams and interactive visualizations:"
        )
        for file_path in updated_files:
            print(f"   - {file_path}")

    if added_interactive:
        print(f"\n✨ Added interactive visualizations to {len(added_interactive)} files:")
        for file_path in added_interactive:
            print(f"   - {file_path}")

    if skipped_files:
        print(f"\n⏭️  Skipped {len(skipped_files)} files (already have both sections):")
        for file_path in skipped_files:
            print(f"   - {file_path}")

    total_modified = len(updated_files) + len(added_interactive)
    print(f"\n📊 Total: {total_modified} modified, {len(skipped_files)} skipped")


def main() -> None:
    """Main function."""
    insert_diagrams()


if __name__ == "__main__":
    main()
