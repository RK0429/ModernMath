#!/usr/bin/env python3
"""Fix incorrect translations field format in all files."""

import sys
from pathlib import Path

import frontmatter


def fix_translations_field() -> bool:
    """Fix translations field to include both languages and use .html."""
    content_dir = Path("content")

    fixed_count = 0
    error_count = 0

    # Process all .qmd files
    for qmd_file in content_dir.rglob("*.qmd"):
        # Skip metadata files and index files
        if qmd_file.name == "_metadata.yml":
            continue

        try:
            # Load file
            with open(qmd_file, "r", encoding="utf-8") as f:
                post = frontmatter.load(f)

            # Skip if not in language-specific directory
            if "/ja/" not in str(qmd_file) and "/en/" not in str(qmd_file):
                continue

            # Extract domain and filename
            parts = qmd_file.relative_to(content_dir).parts
            if len(parts) < 2:
                continue

            domain = parts[1] if len(parts) > 2 else ""
            filename = qmd_file.name

            # Skip if no domain (e.g., ja/index.qmd)
            if not domain:
                continue

            # Check if we need to fix translations field
            needs_fix = False

            # Ensure translations field exists and is a dict
            if "translations" not in post.metadata:
                post.metadata["translations"] = {}
                needs_fix = True
            elif not isinstance(post.metadata["translations"], dict):
                # If it's not a dict, replace it
                post.metadata["translations"] = {}
                needs_fix = True

            translations = post.metadata["translations"]

            # Build correct translations paths
            correct_translations = {
                "en": f"../en/{domain}/{filename.replace('.qmd', '.html')}",
                "ja": f"../ja/{domain}/{filename.replace('.qmd', '.html')}",
            }

            # Check if we need to update
            for lang_code, correct_path in correct_translations.items():
                current_path = translations.get(lang_code, "")

                # Fix if missing, points to .qmd, or is incorrect
                if (
                    not current_path
                    or current_path.endswith(".qmd")
                    or current_path != correct_path
                ):
                    translations[lang_code] = correct_path
                    needs_fix = True

            # Save if modified
            if needs_fix:
                with open(qmd_file, "w", encoding="utf-8") as f:
                    f.write(frontmatter.dumps(post))
                fixed_count += 1
                print(f"✅ Fixed translations in {qmd_file.relative_to(content_dir)}")

        except (IOError, OSError, ValueError) as e:
            print(f"❌ Error processing {qmd_file}: {e}")
            error_count += 1

    print("\n📊 Summary:")
    print(f"   Fixed: {fixed_count} files")
    print(f"   Errors: {error_count} files")

    return error_count == 0


if __name__ == "__main__":
    SUCCESS = fix_translations_field()
    sys.exit(0 if SUCCESS else 1)
