#!/usr/bin/env python3
"""
Insert interactive visualizations into Quarto content files with proper placement.
This script ensures interactive visualization sections are always at the end of articles.
"""

from pathlib import Path
from typing import Optional
import frontmatter


def add_interactive_visualization(content: str, node_id: str, is_japanese: bool) -> str:
    """Add interactive visualization section to content if not present."""
    # Check if interactive visualization already exists
    if "## Interactive Visualization" in content or "## インタラクティブ可視化" in content:
        return content

    # Add interactive visualization section
    if is_japanese:
        interactive_section = f"""## インタラクティブ可視化

ローカルナレッジグラフの近傍をインタラクティブに探索：

::: {{.graph-viz data-id="{node_id}" data-width="700" data-height="500"}}
:::

次のことができます：

- ノードを**ドラッグ**してレイアウトを再配置
- マウスホイールで**ズーム**イン/アウト
- ノードに**ホバー**して詳細を表示
"""
    else:
        interactive_section = f"""## Interactive Visualization

Explore the local knowledge graph neighborhood interactively:

::: {{.graph-viz data-id="{node_id}" data-width="700" data-height="500"}}
:::

You can:

- **Drag** nodes to rearrange the layout
- **Zoom** in/out with your mouse wheel
- **Hover** over nodes to see details
"""

    # Append to content
    return content.rstrip() + "\n\n" + interactive_section


def process_file(qmd_file: Path) -> Optional[str]:
    """Process a single .qmd file to add interactive visualization."""
    with open(qmd_file, "r", encoding="utf-8") as f:
        post = frontmatter.load(f)

    if "id" not in post.metadata:
        return None

    node_id = post.metadata["id"]

    # Determine language from path
    is_japanese = "/ja/" in str(qmd_file)

    # Add interactive visualization
    original_content = post.content
    new_content = add_interactive_visualization(original_content, node_id, is_japanese)

    # Check if content changed
    if new_content != original_content:
        post.content = new_content
        with open(qmd_file, "w", encoding="utf-8") as f:
            f.write(frontmatter.dumps(post))
        return "updated"

    return "unchanged"


def insert_diagrams() -> None:
    """Insert interactive visualizations into Quarto content files."""
    content_dir = Path("content")

    if not content_dir.exists():
        print("Error: content directory not found!")
        return

    updated_files = []
    unchanged_files = []

    # Process each .qmd file
    for qmd_file in content_dir.rglob("*.qmd"):
        result = process_file(qmd_file)

        if result == "updated":
            updated_files.append(qmd_file)
        elif result == "unchanged":
            unchanged_files.append(qmd_file)

    # Report results
    if updated_files:
        print(f"✅ Updated {len(updated_files)} files with interactive visualizations")

    if unchanged_files:
        print(f"⏭️  {len(unchanged_files)} files already have interactive visualization sections")

    print(f"\n📊 Total: {len(updated_files)} updated, {len(unchanged_files)} unchanged")


def main() -> None:
    """Main function."""
    insert_diagrams()


if __name__ == "__main__":
    main()
