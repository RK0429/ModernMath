# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

ModernMath is a Mathematics Knowledge Graph Wiki that represents mathematical concepts (axioms, definitions, theorems, examples) as interconnected nodes in a semantic knowledge graph. It uses Quarto for content authoring, RDF/OWL for graph representation, Python for processing, and provides SPARQL querying capabilities.

## Web Interaction Guidelines

- Use MCP tools such as Playwright or Puppeteer when viewing web content.

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
poetry run python scripts/build_graph.py

# Validate all metadata before building
poetry run python scripts/validate_metadata.py

# Validate the generated graph
poetry run python scripts/validate_graph.py

# Generate comprehensive index pages for all domains
poetry run python scripts/generate_index_pages.py
```

### Generating Visualizations

```bash
# Add click directives to Mermaid diagrams (run before generating)
poetry run python scripts/add_mermaid_links.py

# Generate all visualizations in sequence
poetry run python scripts/generate_mermaid.py
poetry run python scripts/generate_pyvis.py
poetry run python scripts/generate_d3_data.py

# Insert both Mermaid diagrams and interactive visualizations into content files
poetry run python scripts/insert_diagrams.py
```

**Note**: The `insert_diagrams.py` script now:

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
poetry run python scripts/build_search_index.py
```

### Managing Translations

```bash
# Update translation status for all files
poetry run python scripts/manage_translations.py update

# Generate translation progress report
poetry run python scripts/manage_translations.py report

# List files by translation status
poetry run python scripts/manage_translations.py list --status=not_started
poetry run python scripts/manage_translations.py list --status=needs_update

# Validate translation metadata consistency
poetry run python scripts/manage_translations.py validate

# Show domain-by-domain statistics
poetry run python scripts/manage_translations.py stats
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

All Python scripts must pass pre-commit checks with proper type annotations:

- **Type hints**: Import from `typing`, annotate all functions, use `Any` for frontmatter posts
- **flake8**: 100-character line limit, ignore E203,W503,W293
- **pylint**: Avoid too-many-locals (>20), too-many-branches (>12), too-many-statements (>50)
- **mypy/pyright**: Strict type checking, explicit casts when needed
- **Refactoring**: Extract helper functions to reduce complexity

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

### Processing Pipeline

1. **Content Parsing** (`scripts/build_graph.py`):
   - Reads `.qmd` files using `python-frontmatter`
   - Extracts metadata and cross-references
   - Builds RDF triples using `rdflib`

2. **Visualization Generation**:
   - **Mermaid**: Static diagrams for each node's local neighborhood
   - **PyVis**: Interactive HTML visualizations (force-directed graphs)
   - **D3.js**: JSON data for client-side rendering

3. **Cross-Reference Resolution** (`scripts/resolve_cross_references.py`):
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

#### Interactive Visualization Path Issues

For GitHub Pages deployments with project subdirectories, the graph-viz extension calculates relative paths dynamically to ensure visualizations load correctly from any nested directory level.

#### Mermaid Diagram Navigation

Add click directives to enable navigation: `click node-id "relative-path.html" "tooltip-text"`

The `scripts/add_mermaid_links.py` script automatically adds click directives with language-aware tooltips.

#### Content Visualization Standards

The project enforces strict placement rules for visualization sections to ensure consistency:

**Visualization Placement Rules**:

- Dependency Graph and Interactive Visualization sections must ALWAYS appear at the end of articles
- These sections must come after all content sections (Examples, Properties, Related Concepts, etc.)
- The order is: 1) Dependency Graph, 2) Interactive Visualization

**Key Scripts**:

1. **`fix_visualization_placement.py`** - Enforces visualization placement standards:

   ```bash
   # Check for misplaced sections
   poetry run python scripts/fix_visualization_placement.py --check

   # Fix placement without updating content
   poetry run python scripts/fix_visualization_placement.py --fix-only

   # Full update with new diagram content
   poetry run python scripts/fix_visualization_placement.py
   ```

2. **`insert_diagrams.py`** - Automatically uses placement fix logic:
   - Inserts both Mermaid dependency graphs and interactive visualizations
   - Ensures proper placement at end of articles
   - Language-aware headers ("Dependency Graph" vs "依存関係グラフ")

**Important**: The build pipeline automatically enforces correct placement via `insert_diagrams.py`.

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
poetry run python scripts/fix_japanese_index.py

# Or use the convenience script that includes all steps
./build-multilingual.sh

# Note: The CI/CD uses the unified build.yml workflow
```

**Important**: The Japanese site requires a post-build fix because Quarto generates `index.html` from `index.qmd` (English content) by default. The `fix_japanese_index.py` script copies `index-ja.html` to `index.html` in the Japanese output directory to ensure the correct content is displayed.

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
- `generate_index_pages.py` generates language-specific content:
  - Uses Japanese domain names and descriptions when `lang="ja"`
  - Translates section headers (定義, 定理, 例) for Japanese
  - Adjusts navigation links to language-specific pages

### CI/CD Pipeline

The project uses a unified `build.yml` workflow:

1. Builds both language versions sequentially
2. Fixes Japanese index page using `scripts/fix_japanese_index.py`
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
            // Dynamic path resolution for nested pages
            (function() {
              var path = window.location.pathname;
              var depth = (path.match(/\//g) || []).length - 1;
              var basePath = '';
              if (path.includes('/en/')) { # or '/ja/' for Japanese config
                var afterLang = path.split('/en/')[1] || '';
                var extraDepth = (afterLang.match(/\//g) || []).length;
                for (var i = 0; i < extraDepth; i++) {
                  basePath += '../';
                }
              }
              basePath = basePath || './';
              var script = document.createElement('script');
              script.src = basePath + 'js/language-switcher.js';
              script.defer = true;
              document.head.appendChild(script);
            })();
          </script>

filters:
  - translation-metadata # Must come after other filters

resources:
  - js # Include JavaScript directory
```

**Usage Notes:**

- The switcher activates on DOMContentLoaded and Quarto's after-render event
- Async translation checking prevents UI blocking
- Debug functions available via `window.ModernMathLanguageSwitcher`
- **Important**: Static paths like `../../js/language-switcher.js` will fail for nested pages. The dynamic path resolution above ensures the script loads correctly from any page depth

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
- **Interactive Visualization Header**: Always use "インタラクティブ可視化"
- **Standardization Script**: Use `scripts/standardize_dependency_headers.py` to fix any inconsistent headers

### Translation Management System

Uses hash-based change detection to track translation status in `translations-status.yml`:

- **Status Categories**: `not_started`, `in_progress`, `completed`, `needs_update`
- **MD5 Hashing**: Detects content changes (excluding front matter)
- **Management Commands**: `update`, `report`, `list --status=X`, `validate`, `stats`
- **RDF Integration**: Adds `hasTranslation` relationships to the knowledge graph
- **Pre-commit Hook**: Only updates timestamps when content actually changes

## Critical Implementation Details

### CI/CD Script Exit Codes

**Important**: Scripts in the CI/CD pipeline should return exit code 0 when no changes are needed. In CI/CD contexts, "no changes required" is a normal success case, not an error. For example, `add_mermaid_links.py` correctly returns 0 whether files were modified or not.

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

1. First: `build_graph.py` (creates knowledge_graph.ttl)
2. Then: `add_mermaid_links.py` (adds click directives to Mermaid diagrams)
3. Then: Visualization scripts (read the .ttl file)
4. Then: `generate_index_pages.py` (creates comprehensive index pages with language support)
5. Then: `resolve_cross_references.py` (needs content to exist)
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
