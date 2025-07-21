#!/usr/bin/env python3
"""
Validate that JavaScript paths will work correctly when deployed to GitHub Pages.

This script checks that the path calculation logic in _quarto-*.yml files
correctly handles the GitHub Pages subdirectory structure.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple


def extract_js_path_logic(config_file: Path) -> str:
    """Extract the JavaScript path calculation logic from a Quarto config file."""
    content = config_file.read_text()

    # Find the JavaScript block that calculates paths
    pattern = r"<script>.*?</script>"
    matches = re.findall(pattern, content, re.DOTALL)

    for match in matches:
        if "basePath" in match and "ModernMath" in match:
            return str(match)

    return ""


def validate_path_calculation(js_code: str) -> List[str]:
    """Validate the path calculation logic handles GitHub Pages correctly."""
    issues = []

    # Check if it accounts for the ModernMath subdirectory
    if "ModernMath" not in js_code:
        issues.append("Path calculation does not account for GitHub Pages subdirectory")

    # Check if it uses filter(Boolean) to remove empty parts
    if "filter(Boolean)" not in js_code and "filter(function(part) { return part" not in js_code:
        issues.append("Path splitting should filter out empty parts")

    # Check if it handles the subdirectory index
    if "indexOf('ModernMath')" not in js_code:
        issues.append("Should check for ModernMath subdirectory in path")

    # Check if it calculates depth correctly
    if "slice(startIndex)" not in js_code and "relevantParts" not in js_code:
        issues.append("Should calculate depth from site root, not absolute path")

    return issues


def test_path_scenarios() -> List[Tuple[str, str, str]]:
    """Test various URL scenarios to ensure correct path calculation."""
    test_cases = [
        # (URL path, expected basePath for JS, description)
        ("/ModernMath/en/index.html", "./", "Root English page on GitHub Pages"),
        ("/ModernMath/ja/index.html", "./", "Root Japanese page on GitHub Pages"),
        ("/ModernMath/en/algebra/def-group.html", "../", "Domain page on GitHub Pages"),
        (
            "/ModernMath/ja/algebra/def-group.html",
            "../",
            "Domain page on GitHub Pages (Japanese)",
        ),
        ("/ModernMath/en/content/en/algebra/def-group.html", "../../", "Deep nested page"),
        ("/en/index.html", "./", "Root English page locally"),
        ("/ja/index.html", "./", "Root Japanese page locally"),
        ("/en/algebra/def-group.html", "../", "Domain page locally"),
    ]

    return test_cases


def simulate_path_calculation(path: str, has_gh_pages: bool = True) -> str:
    """Simulate the JavaScript path calculation logic."""
    path_parts = [p for p in path.split("/") if p]  # Remove empty parts

    # Check if we're on GitHub Pages
    gh_pages_index = -1
    if has_gh_pages:
        try:
            gh_pages_index = path_parts.index("ModernMath")
        except ValueError:
            gh_pages_index = -1

    start_index = gh_pages_index + 1 if gh_pages_index >= 0 else 0

    # Remove HTML filename if present
    if path_parts and path_parts[-1].endswith(".html"):
        path_parts.pop()

    # Calculate depth from site root
    relevant_parts = path_parts[start_index:]
    depth = len(relevant_parts)

    # Build base path
    if depth == 0:
        return "./"
    return "../" * depth


def main() -> int:
    """Main validation function."""
    print("Validating GitHub Pages path configuration...")
    print("=" * 60)

    # Find project root
    current_file = Path(__file__)
    project_root = current_file.parent.parent.parent

    issues_found = False

    # Check both language configurations
    for lang in ["en", "ja"]:
        config_file = project_root / f"_quarto-{lang}.yml"
        if not config_file.exists():
            print(f"❌ Configuration file not found: {config_file}")
            issues_found = True
            continue

        print(f"\nChecking {config_file.name}...")

        # Extract and validate JS code
        js_code = extract_js_path_logic(config_file)
        if not js_code:
            print("❌ Could not find JavaScript path calculation code")
            issues_found = True
            continue

        # Validate the logic
        issues = validate_path_calculation(js_code)
        if issues:
            print(f"❌ Issues found in {config_file.name}:")
            for issue in issues:
                print(f"   - {issue}")
            issues_found = True
        else:
            print("✅ Path calculation logic looks correct")

    # Test path scenarios
    print("\nTesting path calculation scenarios...")
    print("-" * 60)

    test_cases = test_path_scenarios()
    for url_path, expected, description in test_cases:
        has_gh_pages = "ModernMath" in url_path
        calculated = simulate_path_calculation(url_path, has_gh_pages)

        if calculated == expected:
            print(f"✅ {description}")
            print(f"   Path: {url_path} → Base: {calculated}")
        else:
            print(f"❌ {description}")
            print(f"   Path: {url_path}")
            print(f"   Expected: {expected}, Got: {calculated}")
            issues_found = True

    print("\n" + "=" * 60)
    if issues_found:
        print("❌ Validation failed! Please fix the issues above.")
        return 1
    print("✅ All path calculations validated successfully!")
    print("\nThe JavaScript loading should work correctly on GitHub Pages.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
