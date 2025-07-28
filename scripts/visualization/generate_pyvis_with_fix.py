#!/usr/bin/env python3
"""
Generate PyVis Interactive Visualizations with CSS Fix

This script combines PyVis generation with the CSS path fix,
eliminating the need for a separate fix step in the build workflow.
"""

import sys
import subprocess
from pathlib import Path
import logging
import re

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

# Add the project root to the Python path
project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root))


def fix_css_path(html_file: Path) -> bool:
    """
    Fix the incorrect CSS path in a PyVis HTML file.

    Returns True if the file was modified, False otherwise.
    """
    try:
        content = html_file.read_text(encoding="utf-8")

        # Fix the duplicate dist/ in the CSS path
        fixed_pattern = (
            r"https://cdnjs.cloudflare.com/ajax/libs/vis-network/\g<1>/dist/vis-network.min.css"
        )

        # Find and replace using regex
        pattern = re.compile(
            r"https://cdnjs\.cloudflare\.com/ajax/libs/"
            r"vis-network/([\d.]+)/dist/dist/"
            r"vis-network\.min\.css"
        )
        new_content = pattern.sub(fixed_pattern, content)

        if new_content != content:
            html_file.write_text(new_content, encoding="utf-8")
            logger.debug("Fixed CSS path in %s", html_file)
            return True

        return False

    except (IOError, OSError) as e:
        logger.error("Error processing %s: %s", html_file, e)
        return False


def fix_all_css_paths(output_dir: Path) -> int:
    """Fix CSS paths in all PyVis HTML files."""
    if not output_dir.exists():
        logger.warning("Output directory not found: %s", output_dir)
        return 0

    # Find HTML files in both the root and language subdirectories
    html_files = list(output_dir.rglob("*.html"))
    logger.info("Found %d HTML files to check for CSS fixes", len(html_files))

    fixed_count = 0
    for html_file in html_files:
        if fix_css_path(html_file):
            fixed_count += 1

    if fixed_count > 0:
        logger.info("Fixed CSS paths in %d files", fixed_count)

    return fixed_count


def main() -> None:
    """Generate PyVis visualizations and fix CSS paths in one step."""
    # Step 1: Run the original PyVis generation script
    logger.info("Starting PyVis visualization generation...")

    generate_script = project_root / "scripts" / "visualization" / "generate_pyvis.py"

    try:
        # Run the original generation script
        result = subprocess.run(
            [sys.executable, str(generate_script)], capture_output=True, text=True, check=True
        )

        # Log output from the generation script
        if result.stdout:
            for line in result.stdout.strip().split("\n"):
                logger.info("PyVis: %s", line)

    except subprocess.CalledProcessError as e:
        logger.error("PyVis generation failed: %s", e)
        if e.stderr:
            logger.error("Error output: %s", e.stderr)
        sys.exit(1)

    # Step 2: Fix CSS paths
    logger.info("Fixing CSS paths in generated files...")
    output_dir = project_root / "output" / "interactive"
    fixed_count = fix_all_css_paths(output_dir)

    # Summary
    html_files = list(output_dir.rglob("*.html"))
    logger.info(
        "PyVis generation complete: %d visualizations generated, %d CSS paths fixed",
        len(html_files),
        fixed_count,
    )


if __name__ == "__main__":
    main()
