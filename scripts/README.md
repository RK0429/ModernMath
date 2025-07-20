# ModernMath Scripts Documentation

This directory contains Python scripts for managing and building the Mathematics Knowledge Graph Wiki.

## Translation Management System

### Overview

The translation management system tracks and manages translations between English and Japanese content in the ModernMath project. It provides automated tools for:

- Tracking translation status
- Detecting when source files change and translations need updates
- Validating translation metadata consistency
- Generating translation progress reports

### Scripts

#### `manage_translations.py`

Main script for managing translations with the following commands:

##### Update Command

```bash
poetry run python scripts/manage_translations.py update
```

- Scans all content files in source and target languages
- Calculates MD5 hashes of content (excluding front matter)
- Updates translation status based on file existence and content changes
- Automatically detects:
  - Missing translations (`not_started`)
  - Outdated translations (`needs_update`)
  - Completed translations (`completed`)
  - Work in progress (`in_progress`)

##### Report Command

```bash
poetry run python scripts/manage_translations.py report
```

- Generates a summary report of translation status
- Shows percentage completion by language
- Displays statistics for each status category

##### List Command

```bash
poetry run python scripts/manage_translations.py list --status=<status>
```

- Lists all files with a specific translation status
- Status options: `not_started`, `in_progress`, `completed`, `needs_update`
- Useful for finding files that need attention

##### Validate Command

```bash
poetry run python scripts/manage_translations.py validate
```

- Validates front matter consistency between source and translation files
- Checks for:
  - Matching `id` fields
  - Matching `type` fields
  - Presence of required `translations` field
  - Presence of `translation_of` field

##### Stats Command

```bash
poetry run python scripts/manage_translations.py stats
```

- Shows detailed statistics organized by mathematical domain
- Displays completion percentages for each domain
- Formatted as a table for easy reading

#### `translation_graph.py`

Integration module for adding translation relationships to the RDF knowledge graph.

```python
from translation_graph import add_translation_edges

# Add translation edges to an existing RDF graph
add_translation_edges(graph, Path("translations-status.yml"))
```

- Adds `hasTranslation` predicate to the RDF graph
- Creates translation edges between source and translated concepts
- Includes language metadata for each translation

### Translation Status File

The system maintains translation status in `translations-status.yml`:

```yaml
metadata:
  last_updated: "2025-01-20T14:16:41.122730+00:00"
  source_language: en
  target_languages:
    - ja
  version: 1.0.0

translations:
  algebra/def-group.qmd:
    source_hash: 5c93ea5739579e3328fcba2e7345482a
    translations:
      ja:
        status: completed
        translated_hash: 5c93ea5739579e3328fcba2e7345482a
        translated_at: "2025-01-20T14:16:41.122700+00:00"
```

### Status Categories

1. **not_started**: No translation file exists
2. **in_progress**: Translation file exists but marked as work in progress
3. **completed**: Translation finished and content matches source
4. **needs_update**: Source file changed after translation was completed

### Integration with CI/CD

#### GitHub Actions

Two workflows are provided:

1. **translation-check.yml**: Runs on every push/PR affecting content files
   - Updates translation status
   - Validates translations
   - Fails if status file needs updating

2. **translation-report.yml**: Runs weekly or on-demand
   - Generates comprehensive reports
   - Creates GitHub issues if translations need attention
   - Uploads reports as artifacts

#### Pre-commit Hooks

The following hooks are configured in `.pre-commit-config.yaml`:

- `update-translation-status`: Automatically updates status when content files change
- `check-translation-metadata`: Validates translation metadata consistency

### Best Practices

1. **Run status update regularly**: Before committing changes to content files
2. **Check validation**: Ensure all translations have proper metadata
3. **Monitor reports**: Review weekly translation status reports
4. **Update translations promptly**: When source files change, update translations to maintain consistency

### Front Matter Requirements

Each translated file must include:

```yaml
---
title: "群" # Translated title
id: group # Must match source file
type: Definition # Must match source file
translations:
  en: ../en/algebra/def-group.html
  ja: ../ja/algebra/def-group.html
translation_of: en/algebra/def-group.qmd
---
```

### Example Workflow

1. Create or modify a source file in `content/en/`
2. Run `poetry run python scripts/manage_translations.py update`
3. Check which files need translation: `poetry run python scripts/manage_translations.py list --status=not_started`
4. Create translation in `content/ja/` with proper metadata
5. Run update again to mark as completed
6. Validate metadata: `poetry run python scripts/manage_translations.py validate`

## Other Scripts

### `build_graph.py`

Builds the RDF knowledge graph from content files. Now includes translation edges automatically.

### `validate_metadata.py`

Validates YAML front matter in all content files.

### `check_cross_references.py`

Validates cross-references between content files.

### `generate_mermaid.py`

Generates Mermaid diagrams for visualizing the knowledge graph.

### `generate_pyvis.py`

Creates interactive PyVis visualizations of the knowledge graph.

### `generate_d3_data.py`

Exports graph data in D3.js-compatible format.

### `insert_diagrams.py`

Inserts generated diagrams into content files.

### `resolve_cross_references.py`

Resolves and updates cross-references in generated HTML.

### `generate_index_pages.py`

Generates comprehensive index pages for each mathematical domain.
