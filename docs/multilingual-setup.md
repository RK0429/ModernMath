# Multilingual Setup for ModernMath

This document describes how the ModernMath Knowledge Graph Wiki supports multiple languages (English and Japanese).

## Overview

The multilingual implementation uses separate Quarto configuration files for each language, with content organized in language-specific directories. Each language version is built independently and served from subdirectories.

## Directory Structure

```
ModernMath/
├── _quarto.yml          # Original config (kept for compatibility)
├── _quarto-en.yml       # English site configuration
├── _quarto-ja.yml       # Japanese site configuration
├── content/
│   ├── en/             # English content
│   │   ├── algebra/
│   │   ├── analysis/
│   │   └── ...
│   └── ja/             # Japanese content
│       ├── algebra/
│       ├── analysis/
│       └── ...
└── _site/
    ├── index.html      # Language detection/redirect page
    ├── en/             # English site
    └── ja/             # Japanese site
```

## Language-Specific Configuration

### English Configuration (`_quarto-en.yml`)

- Output directory: `_site/en`
- Language: `en`
- Renders only content in `content/en/`

### Japanese Configuration (`_quarto-ja.yml`)

- Output directory: `_site/ja`
- Language: `ja`
- Renders only content in `content/ja/`
- Uses Japanese UI labels (ホーム, 代数学, etc.)

## Content File Structure

Each content file includes language metadata in the YAML frontmatter:

```yaml
---
title: "Definition: Group"  # or "定義：群" for Japanese
id: "def-group"
type: "Definition"
status: "active"
lang: "en"                  # or "ja"
translations:
  ja: "../../ja/algebra/def-group.qmd"  # Link to Japanese version
  # or for Japanese files:
  # en: "../../en/algebra/def-group.qmd"
---
```

## Building the Multilingual Site

### Manual Build

Use the provided build script:

```bash
./build-multilingual.sh
```

This script:

1. Builds the English version using `_quarto-en.yml`
2. Builds the Japanese version using `_quarto-ja.yml`
3. Creates a root `index.html` that redirects based on browser language

### GitHub Actions

The `build-multilingual.yml` workflow automatically builds both language versions on push/PR.

## Language Switching

Users can switch languages using:

1. The language switcher in the navigation bar (🌐 日本語 / 🌐 English)
2. Direct links in the translations metadata
3. The root index.html language selection page

## Adding New Translations

1. **Create the translated file** in the appropriate language directory:

   ```bash
   cp content/en/algebra/def-group.qmd content/ja/algebra/def-group.qmd
   ```

2. **Update the metadata**:
   - Change `lang` field
   - Update `translations` links
   - Translate the title

3. **Translate the content** while keeping:
   - The same `id` field
   - The same cross-reference labels
   - Mathematical notation unchanged

4. **Update translation status** in `translations-status.yml`

## Translation Guidelines

### What to Translate

- Titles and headings
- Definition text
- Explanatory prose
- Navigation labels

### What NOT to Translate

- Mathematical symbols and equations
- Node IDs (`def-group`, etc.)
- Cross-reference labels
- File names

### Mathematical Terms

Use standard Japanese mathematical terminology:

- Group → 群
- Ring → 環
- Field → 体
- Topology → 位相
- etc.

## Helper Scripts

### Setup Script

```bash
poetry run python scripts/translation/setup_multilingual.py --migrate
```

This script:

- Creates language directories
- Migrates existing content to English directory
- Creates build scripts
- Sets up translation tracking

### Future Enhancements

1. **Automatic Translation Status**
   - Script to check which nodes need translation
   - Dashboard showing translation progress

2. **Machine Translation Integration**
   - Initial translations using DeepL/Google Translate API
   - Marked as "machine-translated" for review

3. **Additional Languages**
   - Framework supports adding more languages
   - Create new `_quarto-{lang}.yml` config
   - Add language directory under `content/`

## CSS Styling

The `styles-multilingual.css` file provides:

- Language switcher styling
- Language indicators
- Bilingual content support
- Japanese-specific font adjustments

## Best Practices

1. **Maintain Consistency**
   - Keep the same node structure across languages
   - Use identical IDs for corresponding content
   - Preserve cross-references

2. **Quality Control**
   - Mark machine translations
   - Track translation status
   - Review by native speakers

3. **SEO Considerations**
   - Use appropriate `lang` attributes
   - Include hreflang links
   - Maintain language-specific URLs
