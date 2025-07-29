#!/usr/bin/env python3
"""Remove type prefixes from article titles in both YAML front matter and content."""

import re
from pathlib import Path
from typing import Match

import yaml


def remove_prefix_from_title(title: str, article_type: str, is_japanese: bool = False) -> str:
    """Remove type prefix from title."""
    # Map English types to Japanese equivalents
    japanese_type_map = {
        "Definition": "定義",
        "Theorem": "定理",
        "Example": "例",
        "Axiom": "公理",
        "Proposition": "命題",
        "Lemma": "補題",
        "Corollary": "系",
    }

    # Get the appropriate type string
    type_string = japanese_type_map.get(article_type, article_type) if is_japanese else article_type

    prefixes = [
        f"{type_string}: ",
        f"{type_string}:",
        f"{type_string}：",  # Japanese full-width colon
    ]

    for prefix in prefixes:
        if title.startswith(prefix):
            return title[len(prefix) :]

    return title


def get_japanese_type_string(article_type: str) -> str:
    """Get the Japanese translation of an article type."""
    japanese_type_map = {
        "Definition": "定義",
        "Theorem": "定理",
        "Example": "例",
        "Axiom": "公理",
        "Proposition": "命題",
        "Lemma": "補題",
        "Corollary": "系",
    }
    return japanese_type_map.get(article_type, article_type)


def get_title_patterns(type_string: str) -> list[str]:
    """Build regex patterns for title matching."""
    return [
        rf"^# {re.escape(type_string)}: (.+?)( {{#[^}}]+}})?$",
        rf"^# {re.escape(type_string)}:(.+?)( {{#[^}}]+}})?$",
        rf"^# {re.escape(type_string)}：(.+?)( {{#[^}}]+}})?$",  # Japanese colon
    ]


def needs_yaml_quotes(title: str) -> bool:
    """Check if a title needs quotes in YAML."""
    special_chars = [
        ":",
        "{",
        "}",
        "[",
        "]",
        ",",
        "&",
        "*",
        "#",
        "?",
        "|",
        "-",
        "<",
        ">",
        "=",
        "!",
        "%",
        "@",
        "\\",
    ]
    return any(char in title for char in special_chars)


def format_yaml_title(title: str) -> str:
    """Format a title for YAML with appropriate quoting."""
    if needs_yaml_quotes(title):
        # Use double quotes if the title contains single quotes
        if "'" in title:
            return f'title: "{title}"'
        return f"title: '{title}'"
    return f"title: {title}"


def update_yaml_title(yaml_lines: list[str], new_title: str) -> list[str]:
    """Update the title in YAML lines."""
    new_yaml_lines = []
    for line in yaml_lines:
        if line.startswith("title:"):
            new_yaml_lines.append(format_yaml_title(new_title))
        else:
            new_yaml_lines.append(line)
    return new_yaml_lines


def process_content_only_modification(
    file_path: Path, content: str, yaml_match: Match[str], article_type: str, is_japanese: bool
) -> bool:
    """Process content modification when YAML title doesn't have prefix."""
    content_after_yaml = content[yaml_match.end() :]

    # Get the appropriate type string for content pattern
    type_string = get_japanese_type_string(article_type) if is_japanese else article_type

    # Build pattern with all possible formats
    title_patterns = get_title_patterns(type_string)

    content_modified = False

    def replace_content_title(match: Match[str]) -> str:
        nonlocal content_modified
        content_modified = True
        title_text = match.group(1).strip()
        id_part = match.group(2) or ""
        return f"# {title_text}{id_part}"

    new_content_after_yaml = content_after_yaml
    for pattern in title_patterns:
        new_content_after_yaml = re.sub(
            pattern, replace_content_title, new_content_after_yaml, count=1, flags=re.MULTILINE
        )

    if not content_modified:
        return False

    # Update file with modified content
    new_content = content[: yaml_match.end()] + new_content_after_yaml
    file_path.write_text(new_content, encoding="utf-8")
    return True


def process_qmd_file(file_path: Path) -> bool:
    """Process a single .qmd file to remove title prefixes.

    Returns True if the file was modified, False otherwise.
    """
    content = file_path.read_text(encoding="utf-8")

    # Extract YAML front matter
    yaml_match = re.match(r"^---\n(.*?)\n---\n", content, re.DOTALL)
    if not yaml_match:
        return False

    yaml_content = yaml_match.group(1)
    try:
        metadata = yaml.safe_load(yaml_content)
    except yaml.YAMLError:
        print(f"Error parsing YAML in {file_path}")
        return False

    if not metadata or "type" not in metadata or "title" not in metadata:
        return False

    article_type = metadata["type"]
    original_title = metadata["title"]

    # Check if this is a Japanese file
    is_japanese = "/ja/" in str(file_path)

    # Remove prefix from YAML title
    new_title = remove_prefix_from_title(original_title, article_type, is_japanese)

    if new_title == original_title:
        # No prefix found, check content for modifications
        return process_content_only_modification(
            file_path, content, yaml_match, article_type, is_japanese
        )

    # Update metadata
    metadata["title"] = new_title

    # Rebuild YAML front matter
    yaml_lines = yaml_content.strip().split("\n")
    new_yaml_lines = update_yaml_title(yaml_lines, new_title)
    new_yaml_content = "\n".join(new_yaml_lines)

    # Update content title
    content_after_yaml = content[yaml_match.end() :]

    # Get the appropriate type string for content pattern
    japanese_type_map = {
        "Definition": "定義",
        "Theorem": "定理",
        "Example": "例",
        "Axiom": "公理",
        "Proposition": "命題",
        "Lemma": "補題",
        "Corollary": "系",
    }
    type_string = japanese_type_map.get(article_type, article_type) if is_japanese else article_type

    # Replace prefixed titles in content
    # Build patterns with all possible formats
    title_patterns = [
        rf"^# {re.escape(type_string)}: (.+?)( {{#[^}}]+}})?$",
        rf"^# {re.escape(type_string)}:(.+?)( {{#[^}}]+}})?$",
        rf"^# {re.escape(type_string)}：(.+?)( {{#[^}}]+}})?$",  # Japanese colon
    ]

    for pattern in title_patterns:
        content_after_yaml = re.sub(
            pattern,
            lambda m: f"# {m.group(1).strip()}{m.group(2) or ''}",
            content_after_yaml,
            count=1,
            flags=re.MULTILINE,
        )

    # Pattern 2: # Title (already without prefix, just ensure it matches new title)
    # This handles cases where content title might not have prefix

    # Rebuild complete content
    new_content = f"---\n{new_yaml_content}\n---\n{content_after_yaml}"

    # Write back to file
    file_path.write_text(new_content, encoding="utf-8")
    return True


def main() -> None:
    """Process all .qmd files to remove title prefixes."""
    # Find all .qmd files in content directory
    content_dir = Path("content")
    if not content_dir.exists():
        print("Content directory not found")
        return

    qmd_files = list(content_dir.rglob("*.qmd"))
    print(f"Found {len(qmd_files)} .qmd files")

    modified_count = 0
    for file_path in qmd_files:
        # Skip index files
        if file_path.name == "index.qmd":
            continue

        try:
            if process_qmd_file(file_path):
                modified_count += 1
                print(f"✓ Modified: {file_path}")
        except (IOError, yaml.YAMLError) as e:
            print(f"✗ Error processing {file_path}: {e}")

    print(f"\nModified {modified_count} files")


if __name__ == "__main__":
    main()
