#!/usr/bin/env python3
"""Check for files with incorrect translations field format."""

import sys
from pathlib import Path

import frontmatter


def check_file_translations(qmd_file: Path) -> list[str]:
    """Check a single file for translation issues."""
    try:
        with open(qmd_file, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)

        # Check if translations field exists
        if "translations" not in post.metadata:
            return []

        translations = post.metadata["translations"]

        # Skip if not in language-specific directory
        if "/ja/" not in str(qmd_file) and "/en/" not in str(qmd_file):
            return []

        issues = []

        # Check if translations is a dict
        if not isinstance(translations, dict):
            return ["translations field is not a dictionary"]

        # Check if all expected languages are present
        expected_langs = {"en", "ja"}
        missing_langs = expected_langs - set(translations.keys())
        if missing_langs:
            issues.append(f"Missing languages: {', '.join(missing_langs)}")

        # Check if pointing to .qmd instead of .html
        for lang, path in translations.items():
            if isinstance(path, str) and path.endswith(".qmd"):
                issues.append(f"{lang} link points to .qmd instead of .html")

        return issues

    except (IOError, OSError, ValueError) as e:
        print(f"❌ Error reading {qmd_file}: {e}")
        return []


def check_translations_format() -> bool:
    """Check all files for incorrect translations field format."""
    content_dir = Path("content")
    incorrect_files = []

    # Check all .qmd files
    for qmd_file in content_dir.rglob("*.qmd"):
        # Skip metadata files
        if qmd_file.name == "_metadata.yml":
            continue

        issues = check_file_translations(qmd_file)
        if issues:
            incorrect_files.append((qmd_file, issues))

    # Report findings
    if incorrect_files:
        print(f"Found {len(incorrect_files)} files with incorrect translations format:\n")
        for file_path, issues in incorrect_files:
            print(f"❌ {file_path.relative_to(content_dir)}:")
            for issue in issues:
                print(f"   - {issue}")
        return False

    print("✅ All files have correct translations format!")
    return True


if __name__ == "__main__":
    SUCCESS = check_translations_format()
    sys.exit(0 if SUCCESS else 1)
