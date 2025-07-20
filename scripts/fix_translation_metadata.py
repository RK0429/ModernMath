#!/usr/bin/env python3
"""Fix missing translation metadata fields in Japanese translation files."""

import sys
from pathlib import Path

import frontmatter


def fix_translation_metadata() -> bool:
    """Add missing translation_of and translations fields to Japanese files."""
    content_dir = Path("content")
    ja_dir = content_dir / "ja"
    en_dir = content_dir / "en"

    if not ja_dir.exists():
        print(f"Japanese content directory not found: {ja_dir}")
        return False

    fixed_count = 0
    error_count = 0

    # Process all Japanese .qmd files
    for ja_file in ja_dir.rglob("*.qmd"):
        # Skip metadata files
        if ja_file.name == "_metadata.yml":
            continue

        try:
            # Load Japanese file
            with open(ja_file, "r", encoding="utf-8") as f:
                post = frontmatter.load(f)

            # Extract domain and filename
            rel_path = ja_file.relative_to(ja_dir)
            domain = rel_path.parts[0] if len(rel_path.parts) > 1 else ""
            filename = rel_path.name

            # Construct English file path
            en_file = en_dir / domain / filename

            if not en_file.exists():
                print(f"⚠️  English source not found for {ja_file.relative_to(content_dir)}")
                error_count += 1
                continue

            # Calculate relative paths for translation_of
            # From ja file to en file: ../../en/domain/filename.qmd
            translation_of_path = f"../../en/{domain}/{filename}"

            # Check if we need to fix anything
            needs_fix = False

            # Add translation_of if missing
            if "translation_of" not in post.metadata:
                post.metadata["translation_of"] = translation_of_path
                needs_fix = True
                print(f"✅ Added translation_of to {ja_file.relative_to(content_dir)}")

            # Add translations field if missing
            if "translations" not in post.metadata:
                # For translations field, we use .html extensions
                post.metadata["translations"] = {
                    "en": f"../en/{domain}/{filename.replace('.qmd', '.html')}",
                    "ja": f"../ja/{domain}/{filename.replace('.qmd', '.html')}",
                }
                needs_fix = True
                print(f"✅ Added translations field to {ja_file.relative_to(content_dir)}")

            # Also ensure the English file has translations field
            with open(en_file, "r", encoding="utf-8") as f:
                en_post = frontmatter.load(f)

            if "translations" not in en_post.metadata:
                en_post.metadata["translations"] = {
                    "en": f"../en/{domain}/{filename.replace('.qmd', '.html')}",
                    "ja": f"../ja/{domain}/{filename.replace('.qmd', '.html')}",
                }
                with open(en_file, "w", encoding="utf-8") as f:
                    f.write(frontmatter.dumps(en_post))
                print(f"✅ Added translations field to {en_file.relative_to(content_dir)}")

            # Save Japanese file if it was modified
            if needs_fix:
                with open(ja_file, "w", encoding="utf-8") as f:
                    f.write(frontmatter.dumps(post))
                fixed_count += 1

        except (IOError, OSError, ValueError) as e:
            print(f"❌ Error processing {ja_file}: {e}")
            error_count += 1

    print("\n📊 Summary:")
    print(f"   Fixed: {fixed_count} files")
    print(f"   Errors: {error_count} files")

    return error_count == 0


if __name__ == "__main__":
    success = fix_translation_metadata()
    sys.exit(0 if success else 1)
