# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

ModernMath is a Mathematics Knowledge Graph Wiki that represents mathematical concepts (axioms, definitions, theorems, examples) as interconnected nodes in a semantic knowledge graph. It uses Quarto for content authoring, RDF/OWL for graph representation, Python for processing, and provides SPARQL querying capabilities.

## Web Interaction Guidelines

- Use MCP tools such as Playwright or Puppeteer when viewing web content.

### Debugging Web UI with Playwright MCP

When debugging web UI issues (e.g., 404 errors, JavaScript problems), use the Playwright MCP tools:

1. **Navigate to the problematic page**:

   ```text
   mcp__playwright__browser_navigate(url="https://example.com/page")
   ```

2. **Get console messages to see errors**:

   ```text
   mcp__playwright__browser_console_messages()
   ```

   This shows all console errors, warnings, and logs with their sources.

3. **Evaluate JavaScript in the browser context**:

   ```text
   mcp__playwright__browser_evaluate(function="() => {
     // Test path calculations or DOM queries
     return {
       path: window.location.pathname,
       calculatedPath: /* your test logic */
     };
   }")
   ```

4. **Take screenshots for visual debugging**:

   ```text
   mcp__playwright__browser_take_screenshot()
   ```

5. **Get page structure snapshot**:
   The browser_navigate response includes a YAML-formatted page snapshot showing the DOM structure, which is useful for understanding element hierarchy and finding selectors.

**Example debugging workflow for 404 errors**:

- Navigate to the page with the error
- Check console messages to see exact resource URLs failing
- Use browser_evaluate to test path calculation logic
- Verify fixes by checking if console errors disappear after changes

## Essential Commands

### Development Setup

```bash
# Install dependencies (requires Poetry)
poetry install

# Activate the virtual environment
poetry shell
```

### Building the Knowledge Graph

```bash
# Build the RDF knowledge graph from content files
poetry run python scripts/graph/build_graph.py

# Validate all metadata before building
poetry run python scripts/validation/validate_metadata.py

# Validate the generated graph
poetry run python scripts/graph/validate_graph.py

# Generate comprehensive index pages for all domains
poetry run python scripts/site/generate_index_pages.py
```

### Generating Visualizations

```bash
# Add click directives to Mermaid diagrams (run before generating)
poetry run python scripts/visualization/add_mermaid_links.py

# Generate all visualizations in sequence
poetry run python scripts/visualization/generate_mermaid.py
poetry run python scripts/visualization/generate_pyvis.py
poetry run python scripts/visualization/generate_d3_data.py

# Insert both Mermaid diagrams and interactive visualizations into content files
poetry run python scripts/visualization/insert_diagrams.py
```

**Note**: The `visualization/insert_diagrams.py` script now:

- Inserts both Mermaid dependency graphs and interactive D3.js visualizations
- Handles files that already have Mermaid diagrams but are missing interactive visualizations
- Respects language context (Japanese vs English) for headers and descriptions

### Site Development

```bash
# Preview the site locally
quarto preview

# Build the complete site
quarto render

# Build with language profiles (for multilingual support)
quarto render --profile en  # Uses _quarto-en.yml automatically
quarto render --profile ja  # Uses _quarto-ja.yml automatically

# Build search index
poetry run python scripts/site/build_search_index.py
```

### Managing Translations

```bash
# Update translation status for all files
poetry run python scripts/translation/manage_translations.py update

# Generate translation progress report
poetry run python scripts/translation/manage_translations.py report

# List files by translation status
poetry run python scripts/translation/manage_translations.py list --status=not_started
poetry run python scripts/translation/manage_translations.py list --status=needs_update

# Validate translation metadata consistency
poetry run python scripts/translation/manage_translations.py validate

# Show domain-by-domain statistics
poetry run python scripts/translation/manage_translations.py stats
```

**Translation Status Categories:**

- `not_started`: No translation file exists
- `in_progress`: Translation file exists but marked incomplete
- `completed`: Translation finished and verified
- `needs_update`: Source changed after translation

The system uses MD5 hashes to detect content changes and automatically updates status in `translations-status.yml`. Translation edges are added to the RDF graph as `hasTranslation` relationships.

### Code Quality

```bash
# Format code
poetry run black scripts/

# Run linting
poetry run flake8 scripts/ --max-line-length=100 --extend-ignore=E203,W503,W293

# Type checking
poetry run mypy scripts/
```

#### Code Quality Requirements

All Python scripts must pass pre-commit checks: proper type annotations from `typing`, flake8 (100-char limit, ignore E203,W503,W293), pylint complexity limits, strict mypy/pyright checks.

### SPARQL and API

```bash
# Start Fuseki SPARQL endpoint
cd fuseki/scripts && ./start_fuseki.sh

# Start REST API
cd api && ./start_api.sh  # Runs on http://localhost:5001/
```

## Architecture Overview

### Content Structure

All mathematical content is in `content/` organized by domain. Each `.qmd` file represents a node in the knowledge graph with:

- **YAML Front Matter**: Contains metadata (id, type, status, requires)
  - **type**: Must be one of: `Corollary`, `Definition`, `Theorem`, `Example`, `Axiom`, `Proposition`, `Lemma` (capitalized)
  - **status**: Must be one of: `verified`, `stub`, `complete`, `draft`
- **Cross-References**: Use `@label` syntax to create graph edges
- **File Naming**: `def-*.qmd`, `thm-*.qmd`, `ex-*.qmd`, `ax-*.qmd`

### Script Organization

Python scripts are organized into functional subdirectories:

- **graph/**: Knowledge graph and RDF operations (build, validate, query)
- **visualization/**: Diagram generation (Mermaid, PyVis, D3.js)
- **translation/**: Multilingual support and translation management
- **validation/**: Content validation and consistency checks
- **site/**: Site building, index pages, and cross-reference resolution
- **experimental/**: Experimental features (LLM integration, Lean support)

**Path Navigation**: Scripts in subdirectories must navigate correctly to project root. For example, scripts in `scripts/visualization/` need `Path(__file__).parent.parent.parent` to reach project root.

### Processing Pipeline

1. **Content Parsing** (`scripts/graph/build_graph.py`):
   - Reads `.qmd` files using `python-frontmatter`
   - Extracts metadata and cross-references
   - Builds RDF triples using `rdflib`

2. **Visualization Generation**:
   - **Mermaid**: Static diagrams for each node's local neighborhood
   - **PyVis**: Interactive HTML visualizations (force-directed graphs)
   - **D3.js**: JSON data for client-side rendering

3. **Cross-Reference Resolution** (`scripts/site/resolve_cross_references.py`):
   - Handles inter-domain references
   - Updates relative paths in generated HTML

### Knowledge Graph Schema

The ontology (`ontology/math-ontology.ttl`) defines:

- **Node Types**: Axiom, Definition, Theorem, Example
- **Relationships**: uses, hasExample, generalizes, implies
- **Mapped to**: OntoMathPRO and SKOS for interoperability

### Key Integration Points

- **Quarto Filter**: `_extensions/graph-viz/` for embedding visualizations
- **GitHub Actions**: Automated build/test/deploy pipeline
- **Fuseki**: SPARQL endpoint for graph queries
- **Flask API**: REST interface for common queries

### Visualization Troubleshooting

- **Path Issues**: graph-viz extension handles relative paths dynamically for GitHub Pages
- **Mermaid Navigation**: Use `click node-id "path.html" "tooltip"` - automated by `add_mermaid_links.py`
- **Placement Rules**: Visualizations must appear at end of articles (Dependency Graph, then Interactive)
- **Key Scripts**: `fix_visualization_placement.py` (enforce standards), `insert_diagrams.py` (auto-placement)

## Multilingual Support

The project supports multiple languages (currently English and Japanese) with automatic language detection and routing.

### Content Structure

- **Language Directories**: `content/en/` for English, `content/ja/` for Japanese
- **Language Profiles**: `_quarto-en.yml` and `_quarto-ja.yml` define language-specific configurations
- **Translation Links**: Each page includes `translations` field in YAML front matter linking to its translations
- **Domain Metadata**: Each domain requires `_metadata.yml` with translated domain name (e.g., `domain: "代数学"` for algebra)

### Translation Implementation Details

**Required Metadata Fields**:

```yaml
translation_of: ../../en/algebra/def-group.qmd # Japanese files only (points to .qmd)
translations: # Both languages (points to .html)
  en: "../en/algebra/def-group.html"
  ja: "../ja/algebra/def-group.html"
```

**Key Requirements**:

- `translations` must be a dictionary with both `en` and `ja` entries
- Keep cross-references as `.qmd` extensions: `[群の定義](def-group.qmd)`
- Standard terms: Group→群, Ring→環, Field→体, Vector Space→ベクトル空間

### Building Multilingual Sites

```bash
# Build both language versions
quarto render --profile en
quarto render --profile ja

# Fix Japanese index page (copies index-ja.html to index.html)
poetry run python scripts/translation/fix_japanese_index.py

# Or use the convenience script that includes all steps
./build-multilingual.sh

# Note: The CI/CD uses the unified build.yml workflow
```

**Important**: The Japanese site requires a post-build fix because Quarto generates `index.html` from `index.qmd` (English content) by default. The `translation/fix_japanese_index.py` script copies `index-ja.html` to `index.html` in the Japanese output directory to ensure the correct content is displayed.

### Quarto Configuration Merging

**Important**: Quarto merges profile configurations with the base `_quarto.yml` rather than replacing them. To avoid duplicate navigation items in multilingual setups:

- Keep the base `_quarto.yml` minimal (only shared configuration like favicon, GitHub links)
- Define complete navbar configurations in each language profile (`_quarto-en.yml`, `_quarto-ja.yml`)
- Do not include language-specific navigation items in the base configuration
- Ensure all 9 mathematical domains are included in both language navbar configurations

### Python Script Compatibility

All Python scripts handle multilingual paths automatically:

- Scripts detect `content/lang/domain/` structure
- Domain extraction logic accounts for language directories
- Falls back to flat structure for backward compatibility
- `content/generate_index_pages.py` generates language-specific content:
  - Uses Japanese domain names and descriptions when `lang="ja"`
  - Translates section headers (定義, 定理, 例) for Japanese
  - Adjusts navigation links to language-specific pages

### CI/CD Pipeline

The project uses a unified `build.yml` workflow:

1. Builds both language versions sequentially
2. Fixes Japanese index page using `scripts/translation/fix_japanese_index.py`
3. Creates a root `index.html` with automatic language detection
4. Deploys both versions to `_site/en/` and `_site/ja/`
5. Includes .nojekyll file for GitHub Pages compatibility

**Important**: Maintain a single workflow file to avoid redundancy. The build.yml workflow handles all multilingual builds - there's no need for separate language-specific workflows.

### Language Detection

Root index.html provides both automatic detection and manual selection:

- Automatic redirect based on browser language preference
- Manual language selection with flag buttons (🇬🇧/🇯🇵)
- Saves user preference in localStorage for future visits
- Provides visual loading feedback during auto-detection

### Dynamic Language Switching

The project implements a page-level language switcher that redirects to the translated version of the current page:

**Implementation Components:**

1. **JavaScript Language Switcher** (`js/language-switcher.js`):
   - Detects current language from URL path or HTML lang attribute
   - Reads translation metadata from HTML meta tags
   - Falls back to path construction with existence checking
   - Updates navbar language links dynamically
   - Provides visual feedback for unavailable translations

2. **Quarto Filter** (`_extensions/translation-metadata/`):
   - Extracts `translations` field from YAML front matter
   - Converts translation links to HTML meta tags
   - Makes metadata accessible to JavaScript

3. **Visual Feedback for Unavailable Translations**:
   - Disabled state with reduced opacity (0.5)
   - Strikethrough text (e.g., "🌐 <s>日本語</s>")
   - Tooltip explaining unavailability
   - `cursor: not-allowed` styling

**Configuration Requirements:**

```yaml
# In _quarto-en.yml and _quarto-ja.yml
format:
  html:
    include-in-header:
      - text: |
          <script>
            window.siteLanguage = 'en'; # or 'ja' for Japanese
            window.alternateLanguage = 'ja'; # or 'en' for Japanese
            window.alternateLanguageUrl = '../ja/'; # or '../en/' for Japanese
            // Calculate the correct path to js directory based on current location
            (function() {
              var path = window.location.pathname;
              var pathParts = path.split('/');
              var basePath = '';

              // Remove empty parts and the HTML filename
              pathParts = pathParts.filter(function(part) { return part && !part.endsWith('.html'); });

              // Count how many directories deep we are from the root
              var depth = pathParts.length;

              // Build the path with the correct number of '../'
              for (var i = 0; i < depth; i++) {
                basePath += '../';
              }

              basePath = basePath || './';

              // Load language switcher
              var script = document.createElement('script');
              script.src = basePath + 'js/language-switcher.js';
              script.defer = true;
              document.head.appendChild(script);

              // Load issue button
              var issueScript = document.createElement('script');
              issueScript.src = basePath + 'js/issue-button.js';
              issueScript.defer = true;
              document.head.appendChild(issueScript);
            })();
          </script>

filters:
  - translation-metadata # Must come after other filters

resources:
  - js/language-switcher.js
  - js/issue-button.js
```

**Usage Notes:**

- The switcher activates on DOMContentLoaded and Quarto's after-render event
- Async translation checking prevents UI blocking
- Debug functions available via `window.ModernMathLanguageSwitcher`
- **Important**: Uses simple depth-based path calculation to navigate from any nested content directory (e.g., `/ja/content/ja/algebra/`) back to the site root where JS files are located
- **Resources**: JavaScript files must be explicitly listed in the resources section to ensure they are copied during build

### Japanese Navigation Pages

When implementing Japanese support, create these navigation pages with `-ja.qmd` suffix:

- `index-ja.qmd` - Japanese home page (referenced in `_quarto-ja.yml` navbar)
- `search-ja.qmd` - Japanese search interface
- `visualizations-ja.qmd` - Japanese visualizations page
- `about-ja.qmd` - Japanese about page
- `contributing-ja.qmd` - Japanese contributing guide

Update `_quarto-ja.yml` navbar to reference these files and ensure all domain links use Japanese paths (e.g., `../../search-ja.qmd` instead of `../../search.qmd`).

### Japanese Terminology Consistency

To maintain consistency across all Japanese content:

- **Dependency Graph Header**: Always use "依存関係グラフ" (not "依存グラフ")
- **Interactive Visualization Header**: Always use "インタラクティブ可視化" (not "インタラクティブな可視化")
- **Standardization Script**: Use `scripts/translation/standardize_dependency_headers.py` to fix any inconsistent headers
- **Visualization Scripts**: The following scripts must use correct Japanese headers:
  - `fix_visualization_placement.py` - Only includes "依存関係グラフ" in detection keywords
  - `check_visualization_order.py` - Uses correct headers for validation
  - `insert_diagrams.py` - Generates sections with standardized headers

### Translation Management System

Uses hash-based change detection to track translation status in `translations-status.yml`:

- **Status Categories**: `not_started`, `in_progress`, `completed`, `needs_update`
- **MD5 Hashing**: Detects content changes (excluding front matter)
- **Management Commands**: `update`, `report`, `list --status=X`, `validate`, `stats`
- **RDF Integration**: Adds `hasTranslation` relationships to the knowledge graph
- **Pre-commit Hook**: Only updates timestamps when content actually changes

## Critical Implementation Details

### CI/CD Script Exit Codes

**Important**: Scripts in the CI/CD pipeline should return exit code 0 when no changes are needed. In CI/CD contexts, "no changes required" is a normal success case, not an error. For example, `visualization/add_mermaid_links.py` correctly returns 0 whether files were modified or not.

### Cross-Reference Format

When referencing concepts across domains, the resolver transforms paths:

```text
@algebra/def-group → ../algebra/def-group.html
```

### Visualization Data Structure

PyVis graphs include:

- Node positioning via force-directed layout
- Color coding by type (Definition=green, Theorem=blue, etc.)
- Hover information with titles and types

### Build Order Dependencies

1. First: `graph/build_graph.py` (creates knowledge_graph.ttl)
2. Then: `visualization/add_mermaid_links.py` (adds click directives to Mermaid diagrams)
3. Then: Visualization scripts (read the .ttl file)
4. Then: `content/generate_index_pages.py` (creates comprehensive index pages with language support)
5. Then: `content/resolve_cross_references.py` (needs content to exist)
6. Finally: `quarto render` (uses all generated assets)

## Current Status

- **Content**: 101 nodes across 9 mathematical domains
- **Translations**: 101/101 (100%) Japanese translations with automated status tracking
- **Graph**: 276+ RDF triples with full dependency tracking and translation edges
- **Visualizations**: 80 interactive graphs deployed
- **API**: RESTful endpoints for node queries and dependencies
- **CI/CD**: Full automation via GitHub Actions with translation validation
- **Translation Management**: Fully implemented with MD5 hash-based change detection and pre-commit hooks

## Next Phase: Lean Integration

The project is designed for future integration with Lean 4:

- `lean_id` field in YAML for mapping to formal proofs
- Planned LeanDojo integration for dependency extraction
- Verification workflow to compare formal/informal graphs
