# Deployment Guide for Math Knowledge Graph Wiki

This guide explains how to deploy the Math Knowledge Graph Wiki to GitHub Pages or other hosting platforms.

## GitHub Pages Deployment

### Automatic Deployment (Recommended)

The project is configured to automatically deploy to GitHub Pages when you push to the `main` branch. 

1. **Enable GitHub Pages in your repository:**
   - Go to your repository on GitHub
   - Navigate to Settings → Pages
   - Under "Source", select "Deploy from a branch"
   - Choose `gh-pages` branch and `/ (root)` folder
   - Click Save

2. **Push to main branch:**
   ```bash
   git add .
   git commit -m "Update content"
   git push origin main
   ```

3. **Wait for deployment:**
   - The GitHub Action will automatically build and deploy your site
   - Check the Actions tab in your repository to monitor progress
   - Once complete, your site will be available at:
     - `https://[username].github.io/[repository-name]/`

### Manual Deployment

If you need to deploy manually:

1. **Build the site locally:**
   ```bash
   poetry run python scripts/build_graph.py
   poetry run python scripts/generate_mermaid.py
   poetry run python scripts/insert_diagrams.py
   quarto render
   ```

2. **Deploy using GitHub Pages action:**
   ```bash
   git add _site/
   git commit -m "Build site"
   git push origin main
   ```

## Custom Domain Setup

To use a custom domain:

1. **Update the workflow:**
   - Edit `.github/workflows/build.yml`
   - Uncomment the `cname` line and set your domain:
     ```yaml
     cname: mathwiki.yourdomain.com
     ```

2. **Configure DNS:**
   - Add a CNAME record pointing to `[username].github.io`
   - Or add A records pointing to GitHub's IP addresses

3. **Enable HTTPS:**
   - In repository Settings → Pages
   - Check "Enforce HTTPS"

## Alternative Hosting Platforms

### Netlify

1. **Build the site:**
   ```bash
   poetry run python scripts/build_graph.py
   quarto render
   ```

2. **Deploy to Netlify:**
   - Create a `netlify.toml`:
     ```toml
     [build]
       publish = "_site"
     ```
   - Connect your GitHub repository to Netlify
   - Deploy automatically on push

### Vercel

1. **Create `vercel.json`:**
   ```json
   {
     "buildCommand": "poetry install && poetry run python scripts/build_graph.py && quarto render",
     "outputDirectory": "_site",
     "installCommand": "pip install poetry"
   }
   ```

2. **Deploy with Vercel CLI:**
   ```bash
   vercel --prod
   ```

## Including the Knowledge Graph

The built `knowledge_graph.ttl` file is included in the `_site` directory during build. To make it accessible:

1. **Direct download link:**
   - Available at: `/knowledge_graph.ttl`
   - Add a download link in your pages

2. **SPARQL endpoint:**
   - For production, consider hosting Fuseki separately
   - Options: Cloud VM, Docker container, or managed service

## Continuous Deployment Best Practices

1. **Branch Protection:**
   - Protect the `main` branch
   - Require PR reviews before merging
   - Run tests before deployment

2. **Preview Deployments:**
   - Use Netlify or Vercel for PR previews
   - Test changes before merging to main

3. **Monitoring:**
   - Set up uptime monitoring
   - Track 404 errors
   - Monitor build times

## Troubleshooting

### Build Failures

- Check GitHub Actions logs for errors
- Ensure all dependencies are in `poetry.lock`
- Verify Quarto version compatibility

### 404 Errors

- Check that `output-dir: _site` in `_quarto.yml`
- Ensure `.nojekyll` file exists
- Verify file paths are correct

### Large Repository Issues

- Consider using Git LFS for large data files
- Optimize images before committing
- Keep `knowledge_graph.ttl` size reasonable

## Performance Optimization

1. **Cache Static Assets:**
   - Use CDN for images and CSS
   - Enable browser caching

2. **Optimize Build Time:**
   - Use GitHub Actions cache
   - Parallelize build steps where possible

3. **Minimize Site Size:**
   - Compress images
   - Minify CSS/JS
   - Use efficient data formats