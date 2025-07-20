#!/usr/bin/env python3
"""
Setup script for multilingual support in ModernMath.
This script helps migrate existing content to a multilingual structure.
"""

import argparse
import logging
import os
import shutil
from pathlib import Path
from typing import Dict, Optional

import yaml

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")
logger = logging.getLogger(__name__)


def setup_language_directories(base_path: Path) -> None:
    """Create language-specific content directories."""
    content_path = base_path / "content"

    # Create language directories
    en_path = content_path / "en"
    ja_path = content_path / "ja"

    en_path.mkdir(exist_ok=True)
    ja_path.mkdir(exist_ok=True)

    logger.info("Created language directories: %s, %s", en_path, ja_path)


def migrate_existing_content(base_path: Path, source_lang: str = "en") -> None:
    """Migrate existing content files to language-specific directory."""
    content_path = base_path / "content"
    target_path = content_path / source_lang

    # List of domains to migrate
    domains = [
        "algebra",
        "analysis",
        "topology",
        "geometry",
        "logic-set-theory",
        "number-theory",
        "probability-statistics",
        "category-theory",
        "combinatorics",
    ]

    for domain in domains:
        domain_path = content_path / domain
        if domain_path.exists() and domain_path.is_dir():
            target_domain_path = target_path / domain

            if not target_domain_path.exists():
                logger.info("Moving %s to %s", domain_path, target_domain_path)
                shutil.move(str(domain_path), str(target_domain_path))
            else:
                logger.warning("Target path %s already exists, skipping", target_domain_path)


def create_language_template(_base_path: Path, _node_id: str, lang: str) -> str:
    """Create a template for a mathematical concept in a specific language."""
    template_content = {
        "en": """---
title: "{title}"
id: "{node_id}"
type: "{node_type}"
status: "active"
lang: "en"
translations:
  ja: "../ja/{node_id}.qmd"
---

# {title}

## Definition

[Content to be added]

## Properties

[Content to be added]

## Examples

[Content to be added]

## Related Concepts

- [Links to related concepts]
""",
        "ja": """---
title: "{title}"
id: "{node_id}"
type: "{node_type}"
status: "active"
lang: "ja"
translations:
  en: "../en/{node_id}.qmd"
---

# {title}

## 定義

[内容を追加]

## 性質

[内容を追加]

## 例

[内容を追加]

## 関連概念

- [関連概念へのリンク]
""",
    }

    return template_content.get(lang, template_content["en"])


def update_metadata_for_language(
    file_path: Path, lang: str, translations: Optional[Dict[str, str]] = None
) -> None:
    """Update YAML frontmatter to include language metadata."""
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    # Split frontmatter and content
    if content.startswith("---"):
        parts = content.split("---", 2)
        if len(parts) >= 3:
            frontmatter = parts[1]
            body = parts[2]
        else:
            frontmatter = ""
            body = content
    else:
        frontmatter = ""
        body = content

    # Parse YAML
    metadata = yaml.safe_load(frontmatter) if frontmatter else {}

    # Add language metadata
    metadata["lang"] = lang
    if translations:
        metadata["translations"] = translations

    # Reconstruct file
    new_content = f"---\n{yaml.dump(metadata, allow_unicode=True)}---\n{body}"

    with open(file_path, "w", encoding="utf-8") as f:
        f.write(new_content)


def create_build_script(base_path: Path) -> None:
    """Create a build script for multilingual site."""
    script_content = """#!/bin/bash
# Build multilingual ModernMath site

echo "Building multilingual ModernMath site..."

# Build English version
echo "Building English version..."
quarto render --profile en --config _quarto-en.yml

# Build Japanese version
echo "Building Japanese version..."
quarto render --profile ja --config _quarto-ja.yml

# Create root index.html redirect
cat > _site/index.html << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Math Knowledge Graph - 数学知識グラフ</title>
    <script>
        // Detect user language preference
        const userLang = navigator.language || navigator.userLanguage;
        const lang = userLang.startsWith('ja') ? 'ja' : 'en';
        window.location.href = './' + lang + '/index.html';
    </script>
</head>
<body>
    <p>Redirecting to your preferred language...</p>
    <p>言語設定に基づいてリダイレクトしています...</p>
    <p>
        <a href="./en/index.html">English</a> |
        <a href="./ja/index.html">日本語</a>
    </p>
</body>
</html>
EOF

echo "Build complete!"
"""

    script_path = base_path / "build-multilingual.sh"
    with open(script_path, "w", encoding="utf-8") as f:
        f.write(script_content)

    # Make executable
    os.chmod(script_path, 0o755)
    logger.info("Created build script: %s", script_path)


def create_translation_tracker(base_path: Path) -> None:
    """Create a YAML file to track translation status."""
    tracker_content = """# Translation Status Tracker for ModernMath
# Status values: pending, in-progress, completed, review

algebra:
  def-group:
    en: completed
    ja: pending
  def-ring:
    en: completed
    ja: pending
  def-field:
    en: completed
    ja: pending

analysis:
  def-limit:
    en: completed
    ja: pending
  def-continuity:
    en: completed
    ja: pending

topology:
  def-topological-space:
    en: completed
    ja: pending
  def-open-set:
    en: completed
    ja: pending
"""

    tracker_path = base_path / "translations-status.yml"
    with open(tracker_path, "w", encoding="utf-8") as f:
        f.write(tracker_content)

    logger.info("Created translation tracker: %s", tracker_path)


def main() -> None:
    """Main function to setup multilingual support."""
    parser = argparse.ArgumentParser(description="Setup multilingual support for ModernMath")
    parser.add_argument(
        "--migrate", action="store_true", help="Migrate existing content to English directory"
    )
    parser.add_argument(
        "--create-templates", action="store_true", help="Create template files for translations"
    )

    args = parser.parse_args()

    base_path = Path.cwd()

    # Always create language directories
    setup_language_directories(base_path)

    # Migrate existing content if requested
    if args.migrate:
        migrate_existing_content(base_path)

    # Create build script
    create_build_script(base_path)

    # Create translation tracker
    create_translation_tracker(base_path)

    logger.info("Multilingual setup complete!")
    logger.info("Next steps:")
    logger.info("1. Run './build-multilingual.sh' to build both language versions")
    logger.info("2. Start translating content in content/ja/")
    logger.info("3. Update translations-status.yml as you progress")


if __name__ == "__main__":
    main()
