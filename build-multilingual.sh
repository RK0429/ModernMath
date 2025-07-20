#!/bin/bash
# Build multilingual ModernMath site
# Note: The CI/CD pipeline uses .github/workflows/build.yml for automated builds

echo "Building multilingual ModernMath site..."

# Build English version
echo "Building English version..."
quarto render --profile en

# Build Japanese version
echo "Building Japanese version..."
quarto render --profile ja

# Copy the root index.html
cp index.html _site/index.html

# Create .nojekyll file for GitHub Pages
touch _site/.nojekyll

echo "Build complete!"
