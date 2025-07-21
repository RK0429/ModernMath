# Translation Management System

## Overview

This system provides comprehensive tools for managing translations between English and Japanese content in the ModernMath Knowledge Graph Wiki.

## Installation

Dependencies are already included in the project's `pyproject.toml`:

- `pyyaml` - For reading/writing YAML files
- `python-frontmatter` - For parsing Quarto front matter
- `rich` - For beautiful terminal output

## Usage

### Update Translation Status

Scan all content files and update the translation status:

```bash
poetry run python scripts/manage_translations.py update
```

This command:

- Scans all source files (English by default)
- Checks for corresponding translations
- Updates hash values to detect changes
- Marks files as `completed`, `in_progress`, `needs_update`, or `not_started`

### Generate Status Report

Get a summary of translation progress:

```bash
poetry run python scripts/manage_translations.py report
```

Output example:

```
Translation Status Summary
========================================
Total source files: 101
Languages: en (source) → ja

JA:
- Completed: 101 (100.0%)
- In Progress: 0 (0.0%)
- Needs Update: 0 (0.0%)
- Not Started: 0 (0.0%)
```

### List Files by Status

List files with a specific translation status:

```bash
# List completed translations
poetry run python scripts/manage_translations.py list --status=completed

# List files needing translation
poetry run python scripts/manage_translations.py list --status=not_started

# List outdated translations
poetry run python scripts/manage_translations.py list --status=needs_update
```

### Validate Translations

Check front matter consistency between source and translated files:

```bash
poetry run python scripts/manage_translations.py validate
```

This validates:

- ID field matches between source and translation
- Type field matches
- Required translation metadata exists

### View Domain Statistics

Get detailed statistics organized by mathematical domain:

```bash
poetry run python scripts/manage_translations.py stats
```

This displays a table showing completion rates for each domain.

## Translation Status File

The system maintains status in `translations-status.yml`:

```yaml
metadata:
  last_updated: "2025-01-20T14:16:41.122730+00:00"
  source_language: en
  target_languages: [ja]
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

## How It Works

1. **Content Hashing**: The system calculates MD5 hashes of file content (excluding front matter) to detect changes
2. **Status Detection**:
   - `not_started`: Translation file doesn't exist
   - `in_progress`: Translation exists but marked as incomplete
   - `completed`: Translation finished and hashes match
   - `needs_update`: Source file changed after translation
3. **Validation**: Ensures translated files maintain consistent metadata with source files

## Integration with Build Pipeline

The translation status can be integrated into the RDF knowledge graph build process to include translation relationships.

## Future Enhancements

- Machine translation integration for initial drafts
- Translation memory for reusing common phrases
- Web dashboard for translation progress
- Support for additional languages
