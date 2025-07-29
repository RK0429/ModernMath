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
        if soup.find("a", {"class": "bmc-custom-button"}):
            print(f"⏭️  Skipping {html_file} - button already exists")
            return

        # Buy Me a Coffee script with custom button
        button_script = (
            '<a href="https://www.buymeacoffee.com/RK0429" target="_blank" '
            'class="bmc-custom-button" rel="noopener noreferrer">'
            '<img src="https://cdn.buymeacoffee.com/buttons/v2/default-yellow.png" '
            'alt="Buy Me a Coffee" style="height: 36px !important;width: auto !important;" />'
            "</a>"
        )

        # Add custom CSS for the button
        style_tag = soup.new_tag("style")
        style_tag.string = """
        .bmc-custom-button {
            position: fixed;
            bottom: 70px; /* Positioned above Report Issue button */
            right: 20px;
            background-color: #FFDD00;
            color: #000000;
            padding: 4px 4px;
            border-radius: 6px;
            text-decoration: none;
            font-size: 14px;
            font-weight: 500;
            display: inline-flex;
            align-items: center;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            transition: all 0.2s ease;
            z-index: 999; /* Slightly below Report Issue button */
        }

        .bmc-custom-button:hover {
            background-color: #FFD814;
            transform: translateY(-1px);
            box-shadow: 0 4px 8px rgba(0,0,0,0.15);
            text-decoration: none;
        }

        .bmc-custom-button:active {
            transform: translateY(0);
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }

        .bmc-custom-button img {
            height: 16px !important;
            width: auto !important;
            margin: 0;
        }

        /* Mobile responsive */
        @media (max-width: 768px) {
            .bmc-custom-button {
                bottom: 60px;
                right: 10px;
                padding: 8px 12px;
                font-size: 13px;
            }
        }

        /* Hide on print */
        @media print {
            .bmc-custom-button {
                display: none;
            }
        }
        """

        # Add style to head if exists, otherwise create head
        head = soup.find("head")
        if head and isinstance(head, Tag):
            head.append(style_tag)
        else:
            # If no head tag, insert before body
            body = soup.find("body")
            if body and isinstance(body, Tag):
                body.insert(0, style_tag)

        # Parse the button HTML
        button_soup = BeautifulSoup(button_script, "html.parser")
        button_element = button_soup.find("a")

        # Find the best place to insert the button
        # Try to insert before closing body tag
        body = soup.find("body")
        if body and isinstance(body, Tag) and button_element:
            body.append(button_element)
        else:
            # If no body tag, append to the html tag
            html = soup.find("html")
            if html and isinstance(html, Tag) and button_element:
                html.append(button_element)

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
