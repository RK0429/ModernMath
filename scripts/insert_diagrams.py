#!/usr/bin/env python3
"""
Insert generated Mermaid diagrams into Quarto content files.
"""

from pathlib import Path
import frontmatter


def insert_diagrams():
    """Insert Mermaid diagrams into Quarto content files."""
    content_dir = Path("content")
    diagrams_dir = Path("output/mermaid")

    if not diagrams_dir.exists():
        print("Error: No diagrams found in output/mermaid/")
        print("Run generate_mermaid.py first.")
        return

    updated_files = []
    skipped_files = []

    # Process each .qmd file
    for qmd_file in content_dir.rglob("*.qmd"):
        with open(qmd_file, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)

        if "id" not in post.metadata:
            continue

        node_id = post.metadata["id"]
        diagram_file = diagrams_dir / f"{node_id}.mermaid"

        if not diagram_file.exists():
            continue

        # Check if diagram section already exists
        if "## Dependency Graph" in post.content or "## Local Graph" in post.content:
            skipped_files.append(qmd_file)
            continue

        # Read diagram content
        with open(diagram_file, "r", encoding="utf-8") as f:
            diagram_content = f.read()

        # Add diagram section to content
        # Place it before any existing sections that might be at the end
        if "## References" in post.content:
            # Insert before references
            parts = post.content.split("## References")
            new_content = (
                parts[0].rstrip()
                + "\n\n## Dependency Graph\n\n"
                + diagram_content
                + "\n\n## References"
                + parts[1]
            )
        else:
            # Add at the end
            new_content = (
                post.content.rstrip() + "\n\n## Dependency Graph\n\n" + diagram_content
            )

        # Write back
        post.content = new_content
        with open(qmd_file, "w", encoding="utf-8") as f:
            f.write(frontmatter.dumps(post))

        updated_files.append(qmd_file)

    # Report results
    print(f"✅ Updated {len(updated_files)} files with Mermaid diagrams:")
    for f in updated_files:
        print(f"   - {f}")

    if skipped_files:
        print(f"\n⏭️  Skipped {len(skipped_files)} files (already have diagrams):")
        for f in skipped_files:
            print(f"   - {f}")

    print(f"\n📊 Total: {len(updated_files)} updated, {len(skipped_files)} skipped")


def main():
    """Main function."""
    insert_diagrams()


if __name__ == "__main__":
    main()
