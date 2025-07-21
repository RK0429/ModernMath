#!/usr/bin/env python3
"""
Remove incorrect '依存グラフ' sections from Japanese content files.
All articles should only have '依存関係グラフ', not '依存グラフ'.
"""

from pathlib import Path

import frontmatter


def remove_incorrect_sections(content: str) -> tuple[str, int]:
    """
    Remove sections with header '## 依存グラフ' from content.
    Returns updated content and number of sections removed.
    """
    lines = content.split("\n")
    new_lines = []
    sections_removed = 0
    skip_section = False

    for i, line in enumerate(lines):
        # Check if this is the incorrect header
        if line.strip() == "## 依存グラフ":
            skip_section = True
            sections_removed += 1
            continue

        # Check if we're starting a new section (which ends the skipped section)
        if skip_section and line.strip().startswith("##"):
            skip_section = False

        # Only add lines that aren't part of the skipped section
        if not skip_section:
            new_lines.append(line)

    return "\n".join(new_lines), sections_removed


def process_japanese_files() -> None:
    """Process all Japanese .qmd files to remove incorrect dependency sections."""
    content_dir = Path("content/ja")

    if not content_dir.exists():
        print(f"Error: Directory {content_dir} not found")
        return

    total_files = 0
    updated_files = 0
    total_sections_removed = 0

    # Process all .qmd files in Japanese content
    for qmd_file in content_dir.rglob("*.qmd"):
        total_files += 1

        # Read file
        with open(qmd_file, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)

        # Remove incorrect sections
        updated_content, sections_removed = remove_incorrect_sections(post.content)

        # Write back if changed
        if sections_removed > 0:
            post.content = updated_content
            with open(qmd_file, "w", encoding="utf-8") as f:
                f.write(frontmatter.dumps(post))

            updated_files += 1
            total_sections_removed += sections_removed
            plural = "s" if sections_removed > 1 else ""
            print(f"✅ Updated: {qmd_file} ({sections_removed} section{plural} removed)")

    # Summary
    print("\n📊 Summary:")
    print(f"   Total files scanned: {total_files}")
    print(f"   Files updated: {updated_files}")
    print(f"   Total sections removed: {total_sections_removed}")

    if updated_files == 0:
        print("   ✨ No incorrect '依存グラフ' sections found")
    else:
        print("   ✅ All incorrect '依存グラフ' sections have been removed")


def main() -> None:
    """Main function."""
    print("🔄 Removing incorrect '依存グラフ' sections from Japanese content...\n")
    process_japanese_files()


if __name__ == "__main__":
    main()
