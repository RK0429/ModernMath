# ModernMath Scripts

This directory contains Python scripts for building and managing the ModernMath knowledge graph wiki.

## Directory Structure

Scripts are organized by functionality into the following subdirectories:

### 📊 graph/

Knowledge graph and RDF operations

- `build_graph.py` - Build RDF knowledge graph from content files (includes Lean verification)
- `validate_graph.py` - Validate the generated graph structure
- `query_graph.py` - Query the knowledge graph
- `translation_graph.py` - Manage translation relationships in graph

### 🎨 visualization/

Diagram and visualization generation

- `generate_mermaid.py` - Generate Mermaid diagrams for each node
- `generate_pyvis.py` - Create interactive PyVis visualizations
- `generate_d3_data.py` - Generate D3.js visualization data
- `insert_diagrams.py` - Insert visualizations into content files (with automatic hyperlinks)
- `fix_pyvis_css.py` - Fix CSS issues in PyVis outputs
- `check_visualization_order.py` - Verify visualization section placement
- `fix_visualization_placement.py` - Ensure visualizations appear at article end

### 🌐 translation/

Translation management and multilingual support

- `manage_translations.py` - Main translation management tool
- `fix_translation_metadata.py` - Fix translation metadata issues
- `fix_translations_field.py` - Correct translation field formats
- `check_translations_format.py` - Validate translation formats
- `setup_multilingual.py` - Configure multilingual site structure
- `fix_japanese_index.py` - Fix Japanese index page generation
- `standardize_dependency_headers.py` - Standardize Japanese terminology
- `README_translations.md` - Detailed translation system documentation

### ✅ validation/

Content validation and consistency checks

- `validate_metadata.py` - Validate YAML frontmatter
- `validate_ontology.py` - Check ontology consistency
- `verify_consistency.py` - Verify overall consistency
- `check_cross_references.py` - Validate cross-references

### 🌏 site/

Site building and generation

- `build_search_index.py` - Build search functionality
- `generate_index_pages.py` - Generate domain index pages
- `resolve_cross_references.py` - Resolve inter-domain references

### 🧪 experimental/

Experimental features and integrations

- `llm_integration.py` - LLM integration experiments
- `nl_query.py` - Natural language query interface
- `test_llm_pr_review.py` - LLM-based PR review testing
- `extract_lean_deps.py` - Extract Lean dependencies
- `extract_lean_mappings.py` - Map to Lean theorems
- `test_leandojo.py` - Test LeanDojo integration

## Usage

Scripts should be run from the project root directory using Poetry:

```bash
# Run from project root
poetry run python scripts/graph/build_graph.py
poetry run python scripts/visualization/generate_mermaid.py
poetry run python scripts/translation/manage_translations.py update
# etc.
```

## Build Pipeline Order

The typical build pipeline runs scripts in this order:

1. **Graph Building**

   ```bash
   poetry run python scripts/graph/build_graph.py
   ```

2. **Visualization Generation**

   ```bash
   poetry run python scripts/visualization/generate_mermaid.py
   poetry run python scripts/visualization/generate_pyvis.py
   poetry run python scripts/visualization/generate_d3_data.py
   poetry run python scripts/visualization/insert_diagrams.py
   ```

3. **Site Generation**

   ```bash
   poetry run python scripts/site/generate_index_pages.py
   poetry run python scripts/site/resolve_cross_references.py
   ```

4. **Final Build**

   ```bash
   quarto render
   ```

## Key Functionality

### Translation Management

The translation system provides comprehensive tools for managing multilingual content. See `translation/README_translations.md` for detailed documentation.

Key commands:

```bash
# Update translation status
poetry run python scripts/translation/manage_translations.py update

# Generate translation report
poetry run python scripts/translation/manage_translations.py report

# List files needing translation
poetry run python scripts/translation/manage_translations.py list --status=not_started

# Validate translation metadata
poetry run python scripts/translation/manage_translations.py validate
```

### Content Validation

Ensure content quality with validation scripts:

```bash
# Validate all metadata
poetry run python scripts/validation/validate_metadata.py

# Check cross-references
poetry run python scripts/validation/check_cross_references.py

# Verify overall consistency
poetry run python scripts/validation/verify_consistency.py
```

### Visualization Generation

Generate various types of visualizations:

```bash
# Generate all visualizations
poetry run python scripts/visualization/generate_mermaid.py
poetry run python scripts/visualization/generate_pyvis.py
poetry run python scripts/visualization/generate_d3_data.py

# Insert into content files
poetry run python scripts/visualization/insert_diagrams.py
```

## Development Guidelines

- All scripts should include proper type hints
- Scripts must pass flake8, mypy, and pylint checks
- Use Poetry for dependency management
- Document any new scripts in this README
- Place new scripts in the appropriate subdirectory based on functionality
