#!/usr/bin/env python3
"""
Inject Buy Me a Coffee button into all HTML pages.

This script adds a Buy Me a Coffee button to all generated HTML pages
as part of the build process.
"""

import sys
from pathlib import Path
from typing import List
from bs4 import BeautifulSoup, Tag


def inject_buy_me_coffee_button(html_file: Path) -> None:
    """Inject Buy Me a Coffee button into an HTML file."""
    try:
        # Read the HTML file
        with open(html_file, "r", encoding="utf-8") as f:
            soup = BeautifulSoup(f.read(), "html.parser")

        # Check if button already exists
        if soup.find("script", {"data-name": "bmc-button"}):
            print(f"⏭️  Skipping {html_file} - button already exists")
            return

        # Buy Me a Coffee script
        button_script = (
            '<script type="text/javascript" '
            'src="https://cdnjs.buymeacoffee.com/1.0.0/button.prod.min.js" '
            'data-name="bmc-button" data-slug="RK0429" data-color="#FFDD00" '
            'data-emoji="" data-font="Comic" data-text="Buy me a coffee" '
            'data-outline-color="#000000" data-font-color="#000000" '
            'data-coffee-color="#ffffff"></script>'
        )

        # Create a wrapper div for positioning
        button_wrapper = soup.new_tag("div")
        button_wrapper["style"] = "position: fixed; bottom: 20px; right: 20px; z-index: 9999;"

        # Parse and add the script to the wrapper
        button_soup = BeautifulSoup(button_script, "html.parser")
        script_tag = button_soup.script
        if script_tag is not None:
            button_wrapper.append(script_tag)

        # Find the best place to insert the button
        # Try to insert before closing body tag
        body = soup.find("body")
        if body and isinstance(body, Tag):
            body.append(button_wrapper)
        else:
            # If no body tag, append to the html tag
            html = soup.find("html")
            if html and isinstance(html, Tag):
                html.append(button_wrapper)

        # Write the modified HTML back
        with open(html_file, "w", encoding="utf-8") as f:
            f.write(str(soup))

        print(f"✅ Injected button into {html_file}")

    except (IOError, OSError) as e:
        print(f"❌ Error processing {html_file}: {e}")


def find_html_files(site_dir: Path) -> List[Path]:
    """Find all HTML files in the site directory."""
    html_files = []
    for html_file in site_dir.rglob("*.html"):
        # Skip certain files/directories if needed
        if any(part.startswith(".") for part in html_file.parts):
            continue
        html_files.append(html_file)
    return html_files


def main() -> None:
    """Main function to inject Buy Me a Coffee button into all HTML pages."""
    # Determine project root
    script_dir = Path(__file__).resolve().parent
    project_root = script_dir.parent.parent

    # Site directory
    site_dir = project_root / "_site"

    if not site_dir.exists():
        print(f"❌ Site directory not found: {site_dir}")
        print("   Make sure to run this after 'quarto render'")
        sys.exit(1)

    print(f"🔍 Looking for HTML files in: {site_dir}")

    # Find all HTML files
    html_files = find_html_files(site_dir)
    print(f"📄 Found {len(html_files)} HTML files")

    # Process each file
    for html_file in html_files:
        inject_buy_me_coffee_button(html_file)

    print("✨ Buy Me a Coffee button injection complete!")


if __name__ == "__main__":
    main()
