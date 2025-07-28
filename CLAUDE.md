# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

ModernMath is a Mathematics Knowledge Graph Wiki that represents mathematical concepts (axioms, definitions, theorems, examples) as interconnected nodes in a semantic knowledge graph. It uses Quarto for content authoring, RDF/OWL for graph representation, Python for processing, and provides SPARQL querying capabilities.

## Web Debugging

Use Playwright MCP tools for debugging deployed sites:

- `mcp__playwright__browser_navigate(url)` - Navigate to page
- `mcp__playwright__browser_console_messages()` - View console errors
- `mcp__playwright__browser_evaluate(function)` - Test JS in browser context

## Essential Commands

### Development Setup

```bash
poetry install  # Install dependencies
poetry shell    # Activate virtual environment
```

### Building the Knowledge Graph

```bash
poetry run python scripts/graph/build_graph.py              # Build RDF graph
poetry run python scripts/validation/validate_metadata.py   # Validate metadata
poetry run python scripts/graph/validate_graph.py          # Validate graph
poetry run python scripts/site/generate_index_pages.py     # Generate indices
```

### Generating Visualizations

```bash
# Run in order:
poetry run python scripts/visualization/generate_mermaid.py         # Skips isolated nodes
poetry run python scripts/visualization/generate_pyvis_with_fix.py  # Includes CSS fix
poetry run python scripts/visualization/generate_d3_data.py
poetry run python scripts/visualization/insert_diagrams.py          # Validates content
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
```

**Pre-commit Hook Behavior**: Hooks fix whitespace/EOF issues, update translation status, validate cross-references. When hooks modify files, re-add and retry commit. Use `git commit --no-verify` to bypass.

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

### Content Workflow

When adding/enriching content:

1. **Verify Accuracy**: Web search to verify mathematical facts
2. **Follow Style Guides**: See `/docs/style_guide/`
3. **Add Cross-References**: Use `@domain/concept-id` syntax
4. **Update References**: Search and update existing mentions
5. **Update Index**: Add to domain's index.qmd alphabetically
6. **Validate**: Run `validate_metadata.py`
7. **Bilingual**: Always update both EN and JA versions
8. **Generate Assets**: Run visualization pipeline in order

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

### CI/CD Pipeline

Unified `build.yml` workflow:

1. Code quality and validation checks
2. Knowledge graph generation with optional Lean integration
3. Visualization generation (prevents empty content)
4. Multilingual site rendering (EN/JA)
5. Post-processing and deployment to GitHub Pages

**Build Indicators**: Uses ✓ for success and ⚠ for warnings in CI logs.

**Workflow Timeouts**:

- `build.yml`: 30 min
- `claude.yml`, `claude-code-review.yml`: 20 min
- Other workflows: 10-30 min

### CI/CD Troubleshooting

**Directory Creation**: Always use `parents=True` when creating directories in scripts:

```python
output_dir.mkdir(parents=True, exist_ok=True)  # Creates parent dirs if needed
```

This prevents FileNotFoundError in CI environments where parent directories may not exist.

### Language Features

- **Auto-detection**: Browser preference redirect
- **Manual selection**: Flag buttons (🇬🇧/🇯🇵)
- **Dynamic switching**: Page-level language switcher
- **Visual feedback**: Disabled state for unavailable translations

### Navigation Structure

- English: `nav/en/about.qmd`, `nav/en/contributing.qmd`
- Japanese: `nav/ja/about.qmd`, `nav/ja/contributing.qmd`
- Exception: `index-ja.qmd` remains in root

### Japanese Consistency

- Dependency Graph: "依存関係グラフ"
- Interactive Visualization: "インタラクティブ可視化"

### Translation Management

- **Status tracking**: MD5 hash-based change detection
- **Auto-translate workflow**: Claude Opus for EN↔JA translations
- **Creates PRs**: For human review

## Critical Implementation Details

### GitHub Pages Deployment

- JS files in language directories: `/ModernMath/[en|ja]/js/`
- Use flexible selectors, avoid CORS issues
- Account for subdirectory structure

### CI/CD Script Exit Codes

Scripts return 0 when no changes needed (success case).

### Quarto HTML Rendering

- HTML blocks: Use `{=html}` syntax
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

- **Order**: build_graph → mermaid → pyvis_with_fix → d3_data → insert_diagrams → quarto render
- **Language detection**: Check `/en/` or `/ja/` in paths
- **Placement**: End of articles (Dependency Graph, then Interactive)

## Repository Management

### Going Public Checklist

1. Update LICENSE placeholders
2. Review security (no hardcoded secrets)
3. Check commit history
4. Clean logs (deployment.log, api.log)
5. Add SECURITY.md
6. Verify .gitignore

### Security Best Practices

- Use `${{ secrets.* }}` in workflows
- No absolute paths with usernames
- Exclude logs and generated files

## Current Status

- **Content**: 110+ nodes across 9 domains
- **Translations**: 90%+ Japanese coverage
- **Graph**: 1300+ RDF triples
- **Visualizations**: Auto-generated for all nodes
- **API**: RESTful endpoints
- **CI/CD**: Full automation
- **Translation Management**: MD5 hash-based tracking
