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
            r"https://cdnjs.cloudflare.com/ajax/libs/vis-network/" r"\g<1>/dist/vis-network.min.css"
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
            logger.info(f"Fixed CSS path in {html_file}")
            return True
        else:
            logger.debug(f"No CSS fix needed for {html_file}")
            return False

    except Exception as e:
        logger.error(f"Error processing {html_file}: {e}")
        return False


def main():
    """Fix all PyVis HTML files in the output directory."""
    project_root = Path(__file__).parent.parent
    output_dir = project_root / "output" / "interactive"

    if not output_dir.exists():
        logger.error(f"Output directory not found: {output_dir}")
        return

    html_files = list(output_dir.glob("*.html"))
    logger.info(f"Found {len(html_files)} HTML files to check")

    fixed_count = 0
    for html_file in html_files:
        if fix_css_path(html_file):
            fixed_count += 1

    logger.info(f"Fixed CSS paths in {fixed_count} files")


if __name__ == "__main__":
    main()
