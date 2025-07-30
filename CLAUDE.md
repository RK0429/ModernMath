# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

ModernMath is a Mathematics Knowledge Graph Wiki that represents mathematical concepts (axioms, definitions, theorems, examples) as interconnected nodes in a semantic knowledge graph. It uses Quarto for content authoring, RDF/OWL for graph representation, Python for processing, and provides SPARQL querying capabilities.

**JavaScript Configuration**: Uses ES modules (`"type": "module"` in package.json) with ESLint 9 flat config format. ESLint configuration requires proper ES module imports and `globals` package for environment variables.

## Web Debugging

Use Playwright MCP tools for debugging: `browser_navigate`, `browser_console_messages`, `browser_evaluate`

## Essential Commands

### Development Setup

```bash
poetry install  # Install dependencies
poetry shell    # Activate virtual environment
```

### Building the Knowledge Graph

```bash
poetry run python scripts/graph/build_graph.py              # Build RDF graph (includes Lean verification)
poetry run python scripts/validation/validate_metadata.py   # Validate metadata
poetry run python scripts/graph/validate_graph.py          # Validate graph
poetry run python scripts/site/generate_index_pages.py     # Generate indices
```

### Generating Visualizations

```bash
# Run in order: mermaid → pyvis_with_fix → d3_data → insert_diagrams
poetry run python scripts/visualization/*.py
```

**Note**: Scripts validate content before creation to prevent empty blocks.

### Site Development

```bash
quarto preview                    # Preview locally
quarto render                     # Build site
quarto render --profile en        # Build English version
quarto render --profile ja        # Build Japanese version
poetry run python scripts/site/build_search_index.py
```

### Managing Translations

```bash
poetry run python scripts/translation/manage_translations.py update
# Commands: update, report, list --status=X, validate, stats
```

Uses MD5 hashes to track status: `not_started`, `in_progress`, `completed`, `needs_update`

### Code Quality

```bash
poetry run black scripts/                 # Format
poetry run flake8 scripts/ --max-line-length=100 --extend-ignore=E203,W503,W293
poetry run mypy scripts/                  # Type check
poetry run python scripts/validation/validate_lean_proofs.py  # Validate Lean proofs
```

**Pre-commit Hook Behavior**: Hooks fix whitespace/EOF issues, update translation status, validate cross-references, and validate Lean proofs. When hooks modify files, re-add and retry commit. Use `git commit --no-verify` to bypass.

### SPARQL and API

```bash
cd fuseki/scripts && ./start_fuseki.sh    # Start SPARQL endpoint
cd api && ./start_api.sh                  # Start REST API (port 5001)
```

## Architecture Overview

### Content Structure

Content in `content/` organized by domain. Each `.qmd` file has:

- **YAML Front Matter**: `id`, `type` (Corollary/Definition/Theorem/Example/Axiom/Proposition/Lemma), `status` (verified/stub/complete/draft), `requires` (list, use `[]` for empty)
- **Cross-References**: Use `@label` syntax
- **File Naming**: `def-*.qmd`, `thm-*.qmd`, `ex-*.qmd`, `ax-*.qmd`
- **Titles**: No type prefixes in titles (e.g., use "Group" not "Definition: Group")
- **YAML Quoting**: Use double quotes for titles with apostrophes (e.g., `title: "Lagrange's Theorem"`)

### Article Type Display

Articles automatically display colored type badges based on YAML `type` field:

- **Implementation**: Quarto filter `_extensions/article-type/`
- **Title Processing**: `scripts/site/remove_title_prefixes.py` removes prefixes from both YAML and content headers
- **Badge Colors**: Definition (blue), Theorem (purple), Example (green), Axiom (orange), etc.
- **Bilingual Support**: Script handles Japanese type prefixes (定義, 定理, 例, 公理, 命題, 補題, 系)
- **Punctuation**: Handles multiple formats: `:`, `：` (full-width Japanese colon)

### Content Workflow

1. Verify accuracy (web search)
2. Follow style guides (`/docs/style_guide/`)
3. Add cross-references (`@domain/concept-id`)
4. Update existing mentions
5. Update domain index alphabetically
6. Validate with `validate_metadata.py`
7. Update both EN/JA versions
8. Run visualization pipeline

### Cross-Reference Management

For fundamental concepts:

- **Search**: Use `grep -i` to find all mentions
- **Update**: Add to YAML `requires` and inline references
- **Cross-Domain**: Use simple ID syntax `def-concept` in YAML
- **Inline Refs**: Use `[@label](../domain/file.qmd)` for cross-domain
- **Articles**: Create dedicated articles for multiply-referenced concepts

### Script Organization

Scripts in functional subdirectories:

- **graph/**: RDF operations
- **visualization/**: Diagram generation
- **translation/**: Multilingual support
- **validation/**: Content checks
- **site/**: Site building
- **experimental/**: LLM/Lean features

**Path Navigation**: Use relative paths from script location, never hardcoded absolute paths.

### Processing Pipeline

1. **Content Parsing** (`build_graph.py`): Reads `.qmd`, extracts metadata, builds RDF triples, detects language from paths
2. **Visualization**: Generates Mermaid/PyVis/D3.js in language-specific directories
3. **Cross-Reference Resolution**: Handles inter-domain references in HTML

### Knowledge Graph Schema

Ontology defines:

- **Node Types**: Axiom, Definition, Theorem, Example
- **Relationships**: uses, hasExample, generalizes, implies
- **Mapped to**: OntoMathPRO and SKOS

### Key Integration Points

- **Quarto Filter**: `_extensions/graph-viz/`
- **GitHub Actions**: Automated CI/CD
- **Fuseki**: SPARQL endpoint
- **Flask API**: REST interface

## Multilingual Support

### Content Structure

- **Directories**: `content/en/`, `content/ja/`
- **Profiles**: `_quarto-en.yml`, `_quarto-ja.yml`
- **Translation Links**: `translations` field in YAML
- **Domain Metadata**: `_metadata.yml` with translated names

### Translation Implementation

- Japanese files: `translation_of: ../../en/path.qmd`
- All files: `translations: {en: "path.html", ja: "path.html"}`
- Standard term mappings: Group→群, Field→体, Vector Space→ベクトル空間

### Building Multilingual Sites

```bash
quarto render --profile en
quarto render --profile ja
poetry run python scripts/translation/fix_japanese_index.py
# Or: ./build-multilingual.sh
```

### Quarto Configuration

Keep base `_quarto.yml` minimal. Define complete navbars in language profiles. Include `nav/en/` and `nav/ja/` in render patterns.

**CSS Loading Order**: Design tokens must be loaded first:

```yaml
css:
  - design-tokens.css
  - styles.css
  - styles-multilingual.css
```

### CI/CD Pipeline

**Parallel Build Architecture** (`build.yml`):

- **Concurrency**: `cancel-in-progress: true`, path filtering on relevant changes
- **Jobs**: quality (10m), lean-validation (15m), graph (15m), visualizations (15m), site (20m), deploy (10m)
- **Optimizations**: Poetry cache, parallel scripts with `&` + `wait`, matrix EN/JA builds
- **Runtime**: ~12-15 minutes total

### CI/CD Troubleshooting

**Directory Creation**: Always use `parents=True` when creating directories in scripts:

```python
output_dir.mkdir(parents=True, exist_ok=True)  # Creates parent dirs if needed
```

This prevents FileNotFoundError in CI environments where parent directories may not exist.

### Language Features

- **Detection**: Browser preference, flag buttons (🇬🇧/🇯🇵), page switcher
- **Navigation**: `nav/{lang}/*.qmd` (except `index-ja.qmd` in root)
- **Terms**: Dependency Graph ("依存関係グラフ"), Interactive Visualization ("インタラクティブ可視化")
- **Management**: MD5 hash tracking, Claude Opus auto-translate, PR creation

## Critical Implementation Details

### GitHub Pages Deployment

- JS files in language directories: `/ModernMath/[en|ja]/js/`
- Use flexible selectors, avoid CORS issues
- Account for subdirectory structure

### CI/CD Script Exit Codes

Scripts return 0 when no changes needed (success case).

### Quarto HTML Rendering

- **Raw HTML blocks**: Use ` ```{=html} ` syntax (triple backticks, not colons)
  - Incorrect: `::: {=html}` (will escape HTML)
  - Correct: ` ```{=html} ` (renders raw HTML)
- JS timing: Use `DOMContentLoaded`
- Error handling: User-friendly messages

### Mermaid Diagrams

````markdown
```{mermaid}
%%| fig-cap: "Caption"
graph TD
...
```
````

**Content Validation**: Visualization scripts validate content before creation, preventing empty or invalid blocks.

### Visualization

- **Generation Order**: build_graph → parallel(mermaid, pyvis_with_fix, d3_data) → insert_diagrams → quarto render
- **Parallel Execution**: All three visualization scripts run concurrently for 3x speedup
- **Language detection**: Check `/en/` or `/ja/` in paths
- **Placement**: End of articles (Dependency Graph, then Interactive)

### Interactive Visualization Implementation

**Libraries Used**:

- **D3.js**: Force-directed graphs embedded via Quarto filter (`_extensions/graph-viz/graph-viz.lua`)
- **PyVis**: Network visualizations with vis.js backend (`viz/pyvis_graphs.py`)

**Making Nodes Clickable**:

- **D3.js**: Click handlers with visual feedback in `_extensions/graph-viz/graph-viz.lua`
  - Click navigates, middle-click opens new tab
  - Pointer cursor and hover effects for clickable nodes
- **PyVis**: Language-aware links ("View Article →" / "記事を見る →")
  - Detects article nodes by prefix: `def-`, `thm-`, `ex-`, `ax-`, `prop-`, `lem-`, `cor-`

**Implementation Details**:

- D3.js nodes include `url` field: `{id: "def-group", url: "def-group.html"}`
- Cross-domain URLs use relative paths: `../domain/file.html`
- Domain extracted via `MYMATH.hasDomain` in RDF graph
- Lua filter embeds JS directly in HTML
- Visual feedback: pointer cursor, hover effects, clickability tooltips
- Middle-click support for new tabs

**Directory URL Handling**:

The graph visualization requires special handling for directory URLs (ending with `/`):

- **Issue**: Directory URLs like `/ModernMath/ja/` calculate incorrect base paths
- **Solution**: Detect `isDirectoryUrl` using `currentPath.endsWith('/')`
- **Depth Calculation**:
  - File URLs: Subtract 1 for the HTML file in path depth calculation
  - Directory URLs: Use full path depth without subtraction
  - Multilingual sites: Ensure minimum depth of 1 to navigate up from language directory
- **Implementation**: See `_extensions/graph-viz/graph-viz.lua` lines 209-254

### Global Knowledge Graph Visualization

The root index pages (`index.qmd` and `index-ja.qmd`) display a global visualization of the entire knowledge graph:

- **Location**: Above the "Features" section on both language homepages
- **Implementation**: Uses `graph-viz` shortcode with `data-id="global-graph"`
- **Data Generation**: `create_global_json()` in `generate_d3_data.py` creates `global-graph.json`
- **URL Paths**: Global uses `content/{lang}/{domain}/{article}.html`, domain-specific uses `../{domain}/{article}.html`
- **Node Filtering**: Global graph excludes all external URIs including formal proofs:
  - Only includes nodes from `BASE_URI` (mathematical concepts)
  - `_get_all_graph_nodes()`: Filters to `str(s).startswith(BASE_URI)` only
  - `_get_all_graph_edges()`: Excludes `isVerifiedBy` edges
- **Individual Visualizations**: Article-specific graphs still show formal proof nodes and `isVerifiedBy` relationships

### Formal Proof Visualization

- **Lean 4 Integration**: Uses `isVerifiedBy` relationship
- **Single Source**: ONLY `build_graph.py` creates proof nodes (never use `add_verification_triples.py`)
- **Labels**: "Formal proof of {node_id}" (EN) / "{node_id}の形式的証明" (JA)
- **URLs**: Point to verified node's article, converted for global graph

### Lean 4 Proof Integration

**Architecture**:

- **Lean Files**: `/formal/` directory organized by module (e.g., `/formal/MathKnowledgeGraph/Algebra/Groups.lean`)
- **Mappings**: `lean_mappings.json` links article IDs to Lean proofs with `lean_id`, `module_name`, and `quarto_file`
- **Embedding**: `scripts/site/embed_lean_proofs.py` adds iframe sections to articles with formal proofs
- **Progress Tracking**: `scripts/site/generate_proof_progress.py` creates overview pages showing verification status
- **Validation**: `scripts/validation/validate_lean_proofs.py` ensures all proofs compile correctly

**Lean Proof Validation**:

- **Pre-commit Hook**: Automatically validates Lean files on `formal/**/*.lean` changes
- **CI/CD Job**: `lean-validation` job installs Lean 4 and runs validation in GitHub Actions
- **Common Issues**:
  - Import paths: Use `Mathlib.Topology.Separation.Basic` not `Mathlib.Topology.Separation`
  - Syntax: Use `∀ a ∈ H, ∀ b ∈ H` not `∀ a b ∈ H`
  - Doc comments: Use regular comments for floating documentation without declarations

**Implementation Details**:

- **Auto-detect GitHub Pages URL**: Script detects from git remote, fallback to `GITHUB_PAGES_URL` env var
  - **IMPORTANT**: GitHub Pages always uses lowercase usernames (e.g., `rk0429.github.io` not `RK0429.github.io`)
  - `embed_lean_proofs.py` must convert usernames to lowercase with `.lower()`
- **iframe Integration**: Loads proofs via `https://live.lean-lang.org/#url=<github-pages-url>/formal/<lean-file>`
  - **URL Format**: Must include full module path: `/formal/MathKnowledgeGraph/Algebra/Groups.lean` (not `/formal/Algebra/Groups.lean`)
  - **IMPORTANT**: Lean web editor requires `#url=` parameter, not `#file=` for loading external files
  - **One-time Fix**: `scripts/site/fix_lean_urls.py` available for correcting existing malformed URLs (not part of regular build)
- **Build Process**:
  - Embed Lean proofs: `poetry run python scripts/site/embed_lean_proofs.py` (generates correct lowercase URLs)
  - Generate progress pages: `poetry run python scripts/site/generate_proof_progress.py`
  - Workflow copies `/formal/` to `_site/formal/` for GitHub Pages serving
- **Progress Pages**: `nav/en/proof-progress.qmd` and `nav/ja/proof-progress.qmd` show coverage by type and domain
  - Article links use: `../../content/{lang}/{domain}/{article}.html` (not `.qmd`)
  - Japanese paths: Replace `/content/en/` with `/content/ja/`
- **Navigation**: "Formal Proofs" link added to navbar in both languages

**Adding New Proofs**:

1. Create Lean file in `/formal/MathKnowledgeGraph/<Domain>/<Module>.lean`
2. Add mapping to `lean_mappings.json`
3. Build process auto-embeds proof section and updates progress

## UI Conventions

### Fixed Action Buttons

- **Report Issue** (`js/issue-button.js`): Bottom-right (70px, 20px), z-index 1000
- **Buy Me a Coffee** (`js/buy-me-coffee-button.js`): Bottom-right (20px, 20px), z-index 999
- Both use design tokens and are injected via Quarto's include-in-header

### Mobile Footer (`js/mobile-footer.js`)

- **Display**: Fixed footer on mobile (≤768px) with 3 buttons: Report Issue, Language Switch, Buy Me a Coffee
- **Layout**: `flex: 1` equal width buttons, z-index 1100, 70px bottom padding
- **Features**: Hides floating buttons, language detection, disabled state for unavailable translations

### Design Tokens System

- **Files**: `design-tokens.css`, `design-tokens.js`, `docs/design-tokens.md`
- **Categories**: Colors, typography, spacing (4-64px), layout, animation
- **Usage**: Load CSS first in Quarto configs, use `var(--token-name)` everywhere

### Progress Bar Implementation

- **Styling**: Located in `styles.css:122-273`, uses gradient backgrounds with color-coded completion levels
  - High (≥75%): Green gradient `#10b981 → #059669`
  - Medium (40-74%): Orange gradient `#f59e0b → #d97706`
  - Low (<40%): Red gradient `#ef4444 → #dc2626`
- **Features**: Shimmer animation, rounded corners (12px), box shadows, responsive design
- **HTML Generation**: `generate_proof_progress.py` creates HTML progress bars with:
  - Main container: `.progress-container` with inset shadow
  - Fill bar: `.progress-fill` with percentage-based width
  - Label: `.progress-label` centered with text shadow
  - Compact variant: `.progress-compact` for tables with smaller height (16px)
- **Layout**: Grid system (`.progress-grid`) for domain/type breakdowns, responsive columns

## Repository Management

**Going Public**: Update LICENSE, check security/history, clean logs, add SECURITY.md, verify .gitignore

**Security**: Use `${{ secrets.* }}`, no absolute paths with usernames, exclude logs/generated files

### Git Repository Recovery

If encountering "fatal: unable to read [hash]" errors:

1. **Backup modified files**: `cp modified-files /tmp/backup/`
2. **Clone fresh repository**: `git clone [repo-url] /tmp/fresh-repo`
3. **Replace corrupted .git**: `mv .git .git.corrupted && cp -r /tmp/fresh-repo/.git .`
4. **Restore backed up files**: `cp /tmp/backup/* original-locations`
5. **Verify with**: `git status`

Common corruption indicators: missing blobs in `git fsck`, cache-tree errors, gc.log failures

## Current Status

- **Content**: 110+ nodes across 9 domains
- **Translations**: 90%+ Japanese coverage
- **Graph**: 1300+ RDF triples
- **Visualizations**: Auto-generated for all nodes
- **API**: RESTful endpoints
- **CI/CD**: Full automation
- **Translation Management**: MD5 hash-based tracking
