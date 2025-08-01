# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

ModernMath is a Mathematics Knowledge Graph Wiki that represents mathematical concepts (axioms, definitions, theorems, examples) as interconnected nodes in a semantic knowledge graph. It uses Quarto for content authoring, RDF/OWL for graph representation, Python for processing, and provides SPARQL querying capabilities.

**JavaScript Configuration**: Uses ES modules (`"type": "module"` in package.json) with ESLint 9 flat config format. ESLint configuration requires proper ES module imports and `globals` package for environment variables.

## Essential Commands

### Development Setup

```bash
poetry install      # Install dependencies
poetry shell        # Activate virtual environment
pre-commit install  # Install git hooks (required for pre-commit to run automatically)
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
poetry run python scripts/visualization/generate_pyvis_with_fix.py  # PyVis visualizations
poetry run python scripts/visualization/generate_d3_data.py        # D3.js data files
poetry run python scripts/visualization/insert_diagrams.py         # Insert interactive visualizations
```

**Note**: Scripts validate content before creation to prevent empty blocks.

### Site Development

```bash
quarto preview                    # Preview locally
quarto render                     # Build site
quarto render --profile en        # Build English version
quarto render --profile ja        # Build Japanese version
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
poetry run python scripts/validation/validate_lean_proofs.py  # Validate Lean proofs (uses parallel build)
```

**Pre-commit Hook Behavior**: Hooks fix whitespace/EOF issues, update translation status, validate cross-references, validate Lean proofs, and lint GitHub Actions workflows with `gh actionlint`. When hooks modify files, re-add and retry commit. Use `git commit --no-verify` to bypass. Note: Prettier errors on .qmd files are expected and can be ignored.

### SPARQL and API

```bash
cd fuseki/scripts && ./start_fuseki.sh    # Start SPARQL endpoint
cd api && ./start_api.sh                  # Start REST API (port 5001)
```

**Search Functionality**:

- Website search is handled by Quarto's built-in search (appears in navbar automatically)
- API `/api/search` endpoint uses basic SPARQL queries only
- No custom search implementation needed - Quarto's search is sufficient

## Architecture Overview

### Content Structure

Content in `content/` organized by domain. Each `.qmd` file has:

- **YAML Front Matter**: `id`, `type` (Corollary/Definition/Theorem/Example/Axiom/Proposition/Lemma), `status` (stub/complete/draft - these are the ONLY valid values, never use "verified"), `requires` (list, use `[]` for empty)
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
- **visualization/**: Interactive diagram generation (PyVis, D3.js only)
- **translation/**: Multilingual support
- **validation/**: Content checks
- **site/**: Site building
- **experimental/**: LLM/Lean features

**Path Navigation**: Use relative paths from script location, never hardcoded absolute paths.

### Processing Pipeline

1. **Content Parsing** (`build_graph.py`): Reads `.qmd`, extracts metadata, builds RDF triples, detects language from paths
2. **Visualization**: Generates PyVis/D3.js in language-specific directories
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

### CI/CD Pipeline (`build.yml`)

- **Architecture**: Parallel jobs with `cancel-in-progress: true`, ~12-15min total runtime
- **Jobs**: quality (10m), lean-validation (<1m cached), graph (15m), visualizations (15m), site (20m), deploy (10m)
- **Optimizations**: Poetry cache, parallel scripts (`&` + `wait`), matrix EN/JA builds
- **Conditional Jobs**: Use check jobs for `hashFiles()` conditions:

  ```yaml
  check-lean:
    outputs:
      has-lean-files: ${{ steps.check.outputs.has-lean-files }}
    steps:
      - run: |
          if find formal -name "*.lean" -type f | grep -q .; then
            echo "has-lean-files=true" >> $GITHUB_OUTPUT
          fi
  ```

- **Lean Caching**: Toolchain (`~/.elan`), packages, build artifacts
- **Key Requirements**:
  - Use `${{ }}` for functions in conditionals: `if: ${{ hashFiles('*.lean') != '' }}`
  - Action versions: `@v6` for peter-evans, `@v4` for others
  - Use `$GITHUB_OUTPUT` not deprecated `set-output`
  - Always `mkdir(parents=True)` in Python scripts

### Language Features

- **Detection**: Browser preference, flag buttons (🇬🇧/🇯🇵), page switcher
- **Navigation**: `nav/{lang}/*.qmd` (except `index-ja.qmd` in root)
- **Terms**: Interactive Visualization ("インタラクティブ可視化")
- **Management**: MD5 hash tracking, Claude Opus auto-translate, PR creation

## Critical Implementation Details

### GitHub Pages Deployment

- JS files in language directories: `/ModernMath/[en|ja]/js/`
- Use flexible selectors, avoid CORS issues
- Account for subdirectory structure

### Quarto HTML Rendering

- **Raw HTML blocks**: Use ` ```{=html} ` syntax (triple backticks, not colons)
  - Incorrect: `::: {=html}` (will escape HTML)
  - Correct: ` ```{=html} ` (renders raw HTML)
- JS timing: Use `DOMContentLoaded`
- Error handling: User-friendly messages

**Content Validation**: Visualization scripts validate content before creation, preventing empty or invalid blocks.

### Visualization

- **Generation Order**: build_graph → parallel(pyvis_with_fix, d3_data) → insert_diagrams → quarto render
- **Parallel Execution**: Both visualization scripts run concurrently for speedup
- **Language detection**: Check `/en/` or `/ja/` in paths
- **Placement**: End of articles (Interactive Visualization only)
- **Architecture**: Uses only interactive visualizations (no static Mermaid diagrams)

### Interactive Visualization Implementation

- **Libraries**: D3.js (force-directed via Quarto filter), PyVis (vis.js backend)
- **Clickable Nodes**:
  - D3.js: Click navigates, middle-click new tab, hover effects
  - PyVis: Language-aware links by article prefix (`def-`, `thm-`, etc.)
- **URLs**: Relative paths (`../domain/file.html`), domain via `MYMATH.hasDomain`
- **Directory URLs**: Special handling for paths ending with `/` in depth calculation

### Global Knowledge Graph Visualization

The root index pages (`index.qmd` and `index-ja.qmd`) display a global visualization of the entire knowledge graph:

- **Location**: Above the "Features" section on both language homepages
- **Implementation**: Uses `graph-viz` shortcode with `data-id="global-graph"`
- **Data Generation**: `create_global_json()` in `generate_d3_data.py` creates `global-graph.json`
- **URL Paths**: Global uses `content/{lang}/{domain}/{article}.html`, domain-specific uses `../{domain}/{article}.html`
- **Node Filtering**: Global graph excludes all external URIs:
  - Only includes nodes from `BASE_URI` (mathematical concepts)
  - `_get_all_graph_nodes()`: Filters to `str(s).startswith(BASE_URI)` only
  - `_get_all_graph_edges()`: Excludes `isVerifiedBy` edges (no longer used)
- **Individual Visualizations**: Article-specific graphs show proof status icons on nodes

### Formal Proof Visualization

- **Proof Status Icons**: Only nodes with completed formal proofs display a check mark icon
  - ✔️ **Completed**: Simple check mark displayed for nodes with completed formal proofs
  - No icons shown for warnings, errors, or unimplemented proofs
- **Implementation**:
  - `build_graph.py`: Formal proof node generation disabled (commented out `_add_lean_verification_triples()`)
  - Visualization scripts load `lean_mappings.json` and `lean_validation_results.json`
  - Only `proof_status: "completed"` is included in generated data
  - D3.js: White transparent check mark (✔️) centered on node with `pointer-events: none`
  - PyVis: Check mark shown in tooltip with "Formal proof completed" text

### Lean 4 Proof Integration

- **Structure**: `/formal/MathKnowledgeGraph/<Domain>/<Module>.lean`, mappings in `lean_mappings.json`
- **Validation Status**: ✅ Completed, ⚠️ Warnings, ❌ Errors, 📝 Not implemented
- **Scripts**:
  - `embed_lean_proofs.py`: Adds iframes to articles (lowercase GitHub usernames!)
  - `generate_proof_progress.py`: Creates progress pages with separate article/proof metrics
  - `validate_lean_proofs.py`: Parses Lake output emojis
- **iframe URL**: `https://live.lean-lang.org/#url=<github-pages-url>/formal/<full-path>`
- **Common Issues**: Use full import paths, `∀ a ∈ H, ∀ b ∈ H` syntax
- **Adding Proofs**: Create file → Add to `lean_mappings.json` → Build auto-embeds

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

### Progress Bar and Table Implementation

- **Progress Bars**: Two visualization styles available:
  - **Standard**: Single-color gradient bars with shimmer animation
  - **Band Graphs**: Multi-segment bars showing status breakdown
    - Article Writing: `complete` (green), `draft` (yellow/orange), `stub` (red)
    - Formal Proofs: `completed` (green), `warnings present` (yellow/orange), `errors present` (red), `not implemented` (gray)
    - Percentage always shows completion rate (completed items only), centered on the bar
    - **Important**: Formal proof progress denominator is total articles, not just those with Lean mappings
    - Implementation in `generate_proof_progress.py` via `_generate_band_graph_section()`
    - CSS classes: `.segment-complete`, `.segment-draft`, `.segment-stub`, `.segment-proof-completed`, `.segment-proof-warnings`, `.segment-proof-errors`, `.segment-proof-not-implemented`
    - Band graph segments use absolute positioning with calculated widths based on counts
    - Helper methods `_generate_formal_proof_section_en/ja()` extract proof statistics to avoid linting issues
- **Interactive Tables** (`js/table-sort-filter.js`):
  - Sort by clicking headers (↑/↓)
  - Filter with text input and dropdowns
  - Multilingual support (EN/JA)
  - Styling in `styles.css:118-252`

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
