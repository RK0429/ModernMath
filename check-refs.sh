#!/bin/bash
# Quick script to check cross-references

echo "Checking cross-references in ModernMath project..."
echo "================================================"

# Run the Python validation script
poetry run python scripts/check_cross_references.py "$@"

# Optional: Also run a quick quarto render on a sample file to catch other warnings
if [ "$1" != "--no-render" ]; then
    echo -e "\nRunning sample render check..."
    quarto render content/algebra/def-group.qmd --to html --quiet 2>&1 | grep -i warn || echo "No render warnings in sample file"
fi
