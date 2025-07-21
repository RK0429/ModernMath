#!/usr/bin/env python3
"""Fix translation paths in domain index.qmd files."""

import sys
from pathlib import Path

import frontmatter

# Add the project root to the Python path
project_root = Path(__file__).parent.parent.parent
sys.path.append(str(project_root))


def fix_translation_paths(file_path: Path) -> bool:
    """Fix the translation paths in a domain index.qmd file.

    Args:
        file_path: Path to the index.qmd file

    Returns:
        True if the file was modified, False otherwise
    """
    # Read the file
    with open(file_path, "r", encoding="utf-8") as f:
        post = frontmatter.load(f)

    # Check if translations field exists
    if "translations" not in post.metadata:
        print(f"No translations field in {file_path}")
        return False

    # Determine the domain from the path
    parts = file_path.parts
    lang_idx = parts.index("content") + 1
    domain_idx = lang_idx + 1

    if lang_idx >= len(parts) or domain_idx >= len(parts):
        print(f"Invalid path structure: {file_path}")
        return False

    current_lang = parts[lang_idx]
    domain = parts[domain_idx]

    # Set correct translation paths
    # These paths are relative to the current location
    # From /en/content/en/domain/ we need to go to /ja/content/ja/domain/
    # That's ../../../ja/content/ja/domain/
    old_translations = post.metadata.get("translations", {})
    new_translations = {}

    if current_lang == "en":
        new_translations["en"] = "index.html"  # Current page
        new_translations["ja"] = f"../../../ja/content/ja/{domain}/"
    else:  # ja
        new_translations["en"] = f"../../../en/content/en/{domain}/"
        new_translations["ja"] = "index.html"  # Current page

    # Check if translations changed
    if old_translations == new_translations:
        print(f"No changes needed for {file_path}")
        return False

    # Update the metadata
    post.metadata["translations"] = new_translations

    # Write the file back
    with open(file_path, "w", encoding="utf-8") as f:
        f.write(frontmatter.dumps(post))

    print(f"Updated translations in {file_path}")
    print(f"  Old: {old_translations}")
    print(f"  New: {new_translations}")
    return True


def main() -> None:
    """Fix translation paths in all domain index files."""
    # Find all domain index.qmd files
    content_dir = project_root / "content"
    index_files = list(content_dir.glob("*/*/index.qmd"))

    print(f"Found {len(index_files)} domain index files")

    modified_count = 0
    for index_file in sorted(index_files):
        if fix_translation_paths(index_file):
            modified_count += 1

    print(f"\nModified {modified_count} files")

    if modified_count > 0:
        print("\nPlease rebuild the site to apply the changes")


if __name__ == "__main__":
    main()
