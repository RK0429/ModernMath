#!/usr/bin/env python3
"""
Standardize dependency graph headers in Japanese content files.
Changes "依存グラフ" to "依存関係グラフ" for consistency.
"""

from pathlib import Path
import re


def standardize_headers(content: str) -> tuple[str, int]:
    """
    Replace "## 依存グラフ" with "## 依存関係グラフ" in content.
    Returns updated content and number of replacements made.
    """
    # Pattern to match the header line exactly
    pattern = r"^## 依存グラフ$"
    replacement = r"## 依存関係グラフ"

    # Count replacements
    replacements = len(re.findall(pattern, content, re.MULTILINE))

    # Perform replacement
    updated_content = re.sub(pattern, replacement, content, flags=re.MULTILINE)

    return updated_content, replacements


def process_japanese_files() -> None:
    """Process all Japanese .qmd files to standardize dependency headers."""
    content_dir = Path("content/ja")

    if not content_dir.exists():
        print(f"Error: Directory {content_dir} not found")
        return

    total_files = 0
    updated_files = 0
    total_replacements = 0

    # Process all .qmd files in Japanese content
    for qmd_file in content_dir.rglob("*.qmd"):
        total_files += 1

        # Read file
        with open(qmd_file, "r", encoding="utf-8") as f:
            content = f.read()

        # Standardize headers
        updated_content, replacements = standardize_headers(content)

        # Write back if changed
        if replacements > 0:
            with open(qmd_file, "w", encoding="utf-8") as f:
                f.write(updated_content)

            updated_files += 1
            total_replacements += replacements
            plural = "s" if replacements > 1 else ""
            print(f"✅ Updated: {qmd_file} ({replacements} replacement{plural})")

    # Summary
    print("\n📊 Summary:")
    print(f"   Total files scanned: {total_files}")
    print(f"   Files updated: {updated_files}")
    print(f"   Total replacements: {total_replacements}")

    if updated_files == 0:
        print("   ✨ All files already use the standard header '依存関係グラフ'")


def main() -> None:
    """Main function."""
    print("🔄 Standardizing dependency graph headers in Japanese content...\n")
    process_japanese_files()


if __name__ == "__main__":
    main()
