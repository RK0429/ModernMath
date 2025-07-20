# GitHub Pages Deployment Guide

## Prerequisites Completed ✓
- GitHub Actions workflow configured (`.github/workflows/build.yml`)
- Quarto site configuration ready (`_quarto.yml`)
- Content and scripts in place
- `.nojekyll` file present

## Steps to Enable GitHub Pages

### 1. Enable GitHub Pages in Repository Settings

1. Go to your repository: https://github.com/RK0429/ModernMath
2. Click on **Settings** tab
3. Scroll down to **Pages** section in the left sidebar
4. Under **Source**, select:
   - **Deploy from a branch**
   - **Branch**: `gh-pages` (this will appear after first successful deployment)
   - **Folder**: `/ (root)`
5. Click **Save**

### 2. Trigger the Deployment

Since the workflow is configured to deploy only on pushes to the main branch:

```bash
# If you have uncommitted changes
git add .
git commit -m "Enable GitHub Pages deployment"
git push origin main

# Or if everything is committed, make a small change to trigger deployment
echo "Deployment trigger: $(date)" >> deployment.log
git add deployment.log
git commit -m "Trigger GitHub Pages deployment"
git push origin main
```

### 3. Monitor the Deployment

1. Go to the **Actions** tab in your repository
2. Watch the "Build Math Knowledge Graph" workflow run
3. Look for the "Deploy to GitHub Pages" step (only runs for Python 3.11 on main branch)
4. After successful completion, the `gh-pages` branch will be created

### 4. Verify the Deployment

After the workflow completes successfully:

1. Return to Settings → Pages
2. You should see a green checkmark and the URL: https://RK0429.github.io/ModernMath
3. Click the URL to visit your deployed site

**Note**: The first deployment may take 5-10 minutes to become accessible.

## Troubleshooting

### If the gh-pages branch doesn't appear:
- Ensure you pushed to the `main` branch (not `master` or another branch)
- Check the Actions tab for any workflow failures
- Verify the workflow conditions in `.github/workflows/build.yml` line 154

### If the site shows 404:
- Wait a few more minutes (initial deployment can be slow)
- Check that GitHub Pages is enabled for the `gh-pages` branch
- Verify the `_site/` directory contains `index.html` after build

### Custom Domain (Optional)
To use a custom domain:
1. Uncomment line 161 in `.github/workflows/build.yml`
2. Replace `mathwiki.yourdomain.com` with your domain
3. Add a CNAME record in your DNS settings pointing to `RK0429.github.io`

## Next Steps After Deployment

1. Test the search functionality
2. Verify interactive visualizations load correctly
3. Check that all internal links work
4. Test the SPARQL endpoint integration (if deployed separately)