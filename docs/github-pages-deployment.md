# GitHub Pages Deployment Guide

## Overview

The Math Knowledge Graph Wiki is configured to automatically deploy to GitHub Pages whenever changes are pushed to the main branch.

## Automatic Deployment

The project uses GitHub Actions for continuous deployment:

1. **Trigger**: Deployment occurs automatically when code is pushed to the `main` branch
2. **Build Process**: The workflow (`/.github/workflows/build.yml`) performs the following:
   - Builds the knowledge graph
   - Generates all visualizations (Mermaid, PyVis, D3.js)
   - Renders the Quarto site
   - Deploys to GitHub Pages

## Repository Configuration

To enable GitHub Pages for your repository:

1. Go to your repository on GitHub
2. Navigate to **Settings** → **Pages**
3. Under **Source**, select:
   - **Deploy from a branch**
   - **Branch**: `gh-pages`
   - **Folder**: `/ (root)`
4. Click **Save**

## Custom Domain (Optional)

To use a custom domain:

1. Add your domain in the repository's Pages settings
2. Update `.github/workflows/build.yml` line 149:
   ```yaml
   cname: mathwiki.yourdomain.com
   ```
3. Configure your DNS provider to point to GitHub Pages

## Local Testing

To test the site locally before deployment:

```bash
# Render the site
quarto render

# Serve locally
quarto preview
```

Or use Python's built-in server:

```bash
cd _site
python -m http.server 8000
```

## Deployment Status

Check deployment status:
- **GitHub Actions**: Go to the "Actions" tab in your repository
- **Pages URL**: Once deployed, your site will be available at:
  - `https://[username].github.io/[repository-name]/`
  - Or your custom domain if configured

## Troubleshooting

### Site Not Appearing

1. Ensure GitHub Pages is enabled in repository settings
2. Check that the workflow completed successfully
3. Wait a few minutes for GitHub Pages to update
4. Clear browser cache

### Build Failures

1. Check the Actions tab for error messages
2. Ensure all dependencies are properly specified in `poetry.lock`
3. Verify Quarto version compatibility

### 404 Errors

1. Ensure `.nojekyll` file exists (prevents Jekyll processing)
2. Check that all file paths are correct
3. Verify `_quarto.yml` output directory matches deployment expectations

## Important Files

- `.nojekyll` - Prevents Jekyll processing
- `_config.yml` - GitHub Pages configuration
- `.github/workflows/build.yml` - Deployment workflow
- `_quarto.yml` - Quarto configuration

## Manual Deployment

If needed, you can manually deploy:

```bash
# Build the site
quarto render

# Deploy using gh-pages branch
git checkout -b gh-pages
cp -r _site/* .
git add .
git commit -m "Deploy to GitHub Pages"
git push origin gh-pages
git checkout main
```

However, automatic deployment via GitHub Actions is recommended.