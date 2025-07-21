#!/usr/bin/env python3
"""
Fix PyVis CSS Path Issue

This script fixes the incorrect CSS path in PyVis-generated HTML files.
PyVis 0.3.2 has a bug where it generates a duplicate 'dist/' in the CSS path.
"""

import re
from pathlib import Path
import logging

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


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
            logger.info("Fixed CSS path in %s", html_file)
            return True

        logger.debug("No CSS fix needed for %s", html_file)
        return False

    except (IOError, OSError) as e:
        logger.error("Error processing %s: %s", html_file, e)
        return False


def main() -> None:
    """Fix all PyVis HTML files in the output directory."""
    project_root = Path(__file__).parent.parent
    output_dir = project_root / "output" / "interactive"

    if not output_dir.exists():
        logger.error("Output directory not found: %s", output_dir)
        return

    html_files = list(output_dir.glob("*.html"))
    logger.info("Found %d HTML files to check", len(html_files))

    fixed_count = 0
    for html_file in html_files:
        if fix_css_path(html_file):
            fixed_count += 1

    logger.info("Fixed CSS paths in %d files", fixed_count)


if __name__ == "__main__":
    main()
