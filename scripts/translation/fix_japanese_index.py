#!/usr/bin/env python3
"""Fix Japanese index page after Quarto build.

This script copies index-ja.html to index.html in the Japanese output directory
to ensure the Japanese site displays Japanese content at the root URL.
"""

import shutil
from pathlib import Path


def fix_japanese_index() -> None:
    """Copy index-ja.html to index.html in Japanese output directory."""
    ja_output_dir = Path("_site/ja")

    if not ja_output_dir.exists():
        print(f"Error: Japanese output directory {ja_output_dir} does not exist!")
        return

    index_ja = ja_output_dir / "index-ja.html"
    index_html = ja_output_dir / "index.html"

    if not index_ja.exists():
        print(f"Error: {index_ja} does not exist!")
        return

    # Copy index-ja.html to index.html
    print(f"Copying {index_ja} to {index_html}...")
    shutil.copy2(index_ja, index_html)
    print("Japanese index page fixed successfully!")


if __name__ == "__main__":
    fix_japanese_index()
