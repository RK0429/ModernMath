#!/usr/bin/env python3
"""
Fix Lean 4 proof URLs in Quarto files.

This script corrects the URLs in iframe src attributes and links to ensure they
include the full path to Lean files (including MathKnowledgeGraph directory).
"""

import re
from pathlib import Path
import logging

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


def fix_lean_urls_in_file(file_path: Path) -> bool:
    """
    Fix Lean URLs in a single file.

    Args:
        file_path: Path to the .qmd file

    Returns:
        True if changes were made, False otherwise
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        original_content = content

        # Pattern to match Lean URLs that are missing MathKnowledgeGraph in the path
        # This matches URLs like:
        # https://RK0429.github.io/ModernMath/formal/Algebra/Groups.lean
        # and should transform to:
        # https://RK0429.github.io/ModernMath/formal/MathKnowledgeGraph/Algebra/Groups.lean

        patterns = [
            # Pattern for Algebra module files
            (
                r"(https://RK0429\.github\.io/ModernMath/formal/)"
                r"(?!MathKnowledgeGraph/)"
                r"(Algebra/(?:Groups|Rings|VectorSpaces)\.lean)",
                r"\1MathKnowledgeGraph/\2",
            ),
            # Pattern for Topology module files
            (
                r"(https://RK0429\.github\.io/ModernMath/formal/)"
                r"(?!MathKnowledgeGraph/)(Topology/Basic\.lean)",
                r"\1MathKnowledgeGraph/\2",
            ),
            # Pattern for Logic module files
            (
                r"(https://RK0429\.github\.io/ModernMath/formal/)"
                r"(?!MathKnowledgeGraph/)(Logic/Sets\.lean)",
                r"\1MathKnowledgeGraph/\2",
            ),
            # Pattern for NumberTheory module files
            (
                r"(https://RK0429\.github\.io/ModernMath/formal/)"
                r"(?!MathKnowledgeGraph/)(NumberTheory/Primes\.lean)",
                r"\1MathKnowledgeGraph/\2",
            ),
            # Pattern for Analysis module files
            (
                r"(https://RK0429\.github\.io/ModernMath/formal/)"
                r"(?!MathKnowledgeGraph/)(Analysis/Limits\.lean)",
                r"\1MathKnowledgeGraph/\2",
            ),
        ]

        for pattern, replacement in patterns:
            content = re.sub(pattern, replacement, content)

        if content != original_content:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(content)
            logger.info("Fixed Lean URLs in %s", file_path)
            return True

        logger.debug("No changes needed in %s", file_path)
        return False

    except IOError as e:
        logger.error("Error processing %s: %s", file_path, e)
        return False


def main() -> None:
    """Main entry point."""
    project_root = Path(__file__).parent.parent.parent
    content_dir = project_root / "content"

    # Find all .qmd files
    qmd_files = list(content_dir.rglob("*.qmd"))

    fixed_count = 0
    for qmd_file in qmd_files:
        if fix_lean_urls_in_file(qmd_file):
            fixed_count += 1

    logger.info("Fixed Lean URLs in %d files out of %d total files", fixed_count, len(qmd_files))


if __name__ == "__main__":
    main()
