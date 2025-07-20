# Translation Management System Implementation Plan

## Overview

This document provides a step-by-step implementation plan for the translation management system designed in `design_EN/translation_management.md`. Each task is detailed enough for a junior-level engineer to complete independently.

## Phase 1: Core Infrastructure Setup

### Task 1.1: Create the Translation Status File Structure

**Description**: Create the initial YAML file to track translation status.

**Steps**:

1. Create a new file named `translations-status.yml` in the project root directory
2. Copy this initial template into the file:

   ```yaml
   # Translation status for ModernMath content
   # Generated and updated by scripts/manage_translations.py

   metadata:
     last_updated: null
     source_language: en
     target_languages: [ja]
     version: "1.0.0"

   translations: {}
   ```

3. Commit the file with message: "feat: Add initial translations-status.yml structure"

**Success Criteria**:

- File exists at `/translations-status.yml`
- YAML syntax is valid (test with `poetry run python -c "import yaml; yaml.safe_load(open('translations-status.yml'))"`)

### Task 1.2: Set Up Project Configuration

**Description**: Add translation configuration to pyproject.toml.

**Steps**:

1. Open `pyproject.toml`
2. Add this section at the end of the file:

   ```toml
   [tool.modernmath.translations]
   source_language = "en"
   target_languages = ["ja"]
   status_file = "translations-status.yml"
   ignore_patterns = ["**/index.qmd", "**/_metadata.yml", "**/_extensions/**"]
   ```

3. Validate TOML syntax: `poetry run python -c "import toml; toml.load('pyproject.toml')"`

**Success Criteria**:

- Configuration section exists in pyproject.toml
- TOML file remains valid

## Phase 2: Create the Management Script

### Task 2.1: Create Basic Script Structure

**Description**: Create the main translation management script with basic command structure.

**Steps**:

1. Create file `scripts/manage_translations.py`
2. Add the following code:

   ```python
   #!/usr/bin/env python3
   """
   Translation management system for ModernMath Knowledge Graph Wiki.
   Tracks and manages translation status between languages.
   """

   import argparse
   import hashlib
   import os
   import sys
   from datetime import datetime
   from pathlib import Path
   from typing import Dict, List, Optional, Literal

   import yaml
   import frontmatter
   from rich.console import Console
   from rich.table import Table

   # Initialize console for pretty output
   console = Console()

   # Type definitions
   StatusType = Literal["not_started", "in_progress", "completed", "needs_update"]


   def main():
       """Main entry point for the translation management system."""
       parser = argparse.ArgumentParser(
           description="Manage translations for ModernMath content"
       )

       subparsers = parser.add_subparsers(dest="command", help="Available commands")

       # Add subcommands
       subparsers.add_parser("update", help="Update translation status")
       subparsers.add_parser("report", help="Generate translation report")

       list_parser = subparsers.add_parser("list", help="List files by status")
       list_parser.add_argument(
           "--status",
           choices=["not_started", "in_progress", "completed", "needs_update"],
           required=True,
           help="Filter by translation status"
       )

       subparsers.add_parser("validate", help="Validate all translations")
       subparsers.add_parser("stats", help="Show translation statistics")

       args = parser.parse_args()

       if not args.command:
           parser.print_help()
           sys.exit(1)

       # Command routing
       if args.command == "update":
           console.print("[yellow]Update command not yet implemented[/yellow]")
       elif args.command == "report":
           console.print("[yellow]Report command not yet implemented[/yellow]")
       elif args.command == "list":
           console.print(f"[yellow]List command for status '{args.status}' not yet implemented[/yellow]")
       elif args.command == "validate":
           console.print("[yellow]Validate command not yet implemented[/yellow]")
       elif args.command == "stats":
           console.print("[yellow]Stats command not yet implemented[/yellow]")


   if __name__ == "__main__":
       main()
   ```

3. Make the script executable: `chmod +x scripts/manage_translations.py`
4. Test the script: `poetry run python scripts/manage_translations.py --help`

**Success Criteria**:

- Script runs without errors
- Help message displays all subcommands
- Each command shows "not yet implemented" message

### Task 2.2: Implement File Scanning Functionality

**Description**: Add functions to scan content directories and calculate file hashes.

**Steps**:

1. Add these functions to `scripts/manage_translations.py` after the imports:

   ```python
   def get_content_hash(file_path: Path) -> str:
       """
       Calculate MD5 hash of file content (excluding front matter).

       Args:
           file_path: Path to the content file

       Returns:
           MD5 hash string
       """
       try:
           with open(file_path, 'r', encoding='utf-8') as f:
               post = frontmatter.load(f)
               # Hash only the content, not the metadata
               content = post.content.strip()
               return hashlib.md5(content.encode('utf-8')).hexdigest()
       except Exception as e:
           console.print(f"[red]Error hashing {file_path}: {e}[/red]")
           return ""


   def scan_content_directory(base_path: Path, language: str) -> List[Dict]:
       """
       Scan a language directory for all .qmd files.

       Args:
           base_path: Base content directory path
           language: Language code (e.g., 'en', 'ja')

       Returns:
           List of dictionaries with file information
       """
       content_dir = base_path / language
       files = []

       if not content_dir.exists():
           console.print(f"[red]Directory not found: {content_dir}[/red]")
           return files

       # Find all .qmd files
       for qmd_file in content_dir.rglob("*.qmd"):
           # Skip ignored patterns
           relative_path = qmd_file.relative_to(content_dir)

           # Skip index files and metadata files
           if (qmd_file.name == "index.qmd" or
               qmd_file.name == "_metadata.yml" or
               "_extensions" in str(relative_path)):
               continue

           files.append({
               "path": relative_path,
               "full_path": qmd_file,
               "hash": get_content_hash(qmd_file),
               "language": language
           })

       return files


   def load_status_file(status_file: Path) -> Dict:
       """Load the translation status YAML file."""
       if not status_file.exists():
           return {
               "metadata": {
                   "last_updated": None,
                   "source_language": "en",
                   "target_languages": ["ja"]
               },
               "translations": {}
           }

       with open(status_file, 'r', encoding='utf-8') as f:
           return yaml.safe_load(f) or {}


   def save_status_file(status_file: Path, data: Dict) -> None:
       """Save the translation status YAML file."""
       data["metadata"]["last_updated"] = datetime.utcnow().isoformat() + "Z"

       with open(status_file, 'w', encoding='utf-8') as f:
           yaml.dump(data, f, default_flow_style=False, sort_keys=False)
   ```

2. Test the functions by adding a temporary test at the bottom of main():

   ```python
   # Temporary test
   files = scan_content_directory(Path("content"), "en")
   console.print(f"Found {len(files)} files")
   ```

**Success Criteria**:

- Functions compile without syntax errors
- Running the script shows the number of files found

### Task 2.3: Implement Update Command

**Description**: Implement the `update` command to scan files and update translation status.

**Steps**:

1. Add this function before the main() function:

   ```python
   def update_translation_status(base_path: Path, status_file: Path) -> None:
       """
       Update the translation status by scanning all content files.

       Args:
           base_path: Base content directory
           status_file: Path to translations-status.yml
       """
       console.print("[bold blue]Updating translation status...[/bold blue]")

       # Load current status
       status_data = load_status_file(status_file)
       source_lang = status_data["metadata"]["source_language"]
       target_langs = status_data["metadata"]["target_languages"]

       # Scan source files
       source_files = scan_content_directory(base_path, source_lang)
       console.print(f"Found {len(source_files)} source files in '{source_lang}'")

       # Process each source file
       for source_file in source_files:
           file_key = str(source_file["path"])

           # Initialize entry if not exists
           if file_key not in status_data["translations"]:
               status_data["translations"][file_key] = {
                   "source_hash": source_file["hash"],
                   "translations": {}
               }
           else:
               # Update source hash
               status_data["translations"][file_key]["source_hash"] = source_file["hash"]

           # Check each target language
           for target_lang in target_langs:
               target_path = base_path / target_lang / source_file["path"]

               if file_key not in status_data["translations"]:
                   status_data["translations"][file_key] = {"translations": {}}

               if target_lang not in status_data["translations"][file_key]["translations"]:
                   status_data["translations"][file_key]["translations"][target_lang] = {}

               trans_info = status_data["translations"][file_key]["translations"][target_lang]

               if target_path.exists():
                   target_hash = get_content_hash(target_path)

                   # Determine status
                   if trans_info.get("status") == "completed":
                       # Check if source has changed
                       if trans_info.get("translated_hash") != source_file["hash"]:
                           trans_info["status"] = "needs_update"
                   elif trans_info.get("status") != "in_progress":
                       # Assume completed if file exists and not marked otherwise
                       trans_info["status"] = "completed"
                       trans_info["translated_hash"] = source_file["hash"]
                       trans_info["translated_at"] = datetime.utcnow().isoformat() + "Z"
               else:
                   # Translation doesn't exist
                   trans_info["status"] = "not_started"

       # Save updated status
       save_status_file(status_file, status_data)
       console.print("[green]Translation status updated successfully![/green]")
   ```

2. Update the main() function to call this function:

   ```python
   if args.command == "update":
       update_translation_status(Path("content"), Path("translations-status.yml"))
   ```

**Success Criteria**:

- Running `poetry run python scripts/manage_translations.py update` completes without errors
- `translations-status.yml` is populated with file entries

### Task 2.4: Implement Report Command

**Description**: Implement the `report` command to generate translation status reports.

**Steps**:

1. Add this function:

   ```python
   def generate_report(status_file: Path, format: str = "summary") -> None:
       """Generate translation status report."""
       status_data = load_status_file(status_file)

       if format == "summary":
           # Count statistics
           stats = {lang: {"completed": 0, "in_progress": 0, "needs_update": 0, "not_started": 0}
                   for lang in status_data["metadata"]["target_languages"]}

           total_files = len(status_data["translations"])

           for file_key, file_data in status_data["translations"].items():
               for lang, trans_data in file_data.get("translations", {}).items():
                   status = trans_data.get("status", "not_started")
                   stats[lang][status] += 1

           # Print summary
           console.print("\n[bold]Translation Status Summary[/bold]")
           console.print("=" * 40)
           console.print(f"Total source files: {total_files}")
           console.print(f"Languages: {status_data['metadata']['source_language']} (source) → {', '.join(status_data['metadata']['target_languages'])}")

           for lang, lang_stats in stats.items():
               console.print(f"\n[bold]{lang.upper()}:[/bold]")
               total = sum(lang_stats.values())
               for status, count in lang_stats.items():
                   percentage = (count / total * 100) if total > 0 else 0
                   console.print(f"- {status.replace('_', ' ').title()}: {count} ({percentage:.1f}%)")
   ```

2. Update the main() function:

   ```python
   elif args.command == "report":
       generate_report(Path("translations-status.yml"))
   ```

**Success Criteria**:

- Running `poetry run python scripts/manage_translations.py report` shows a summary
- Statistics are accurate based on the status file

### Task 2.5: Implement List Command

**Description**: Implement the `list` command to show files with specific status.

**Steps**:

1. Add this function:

   ```python
   def list_files_by_status(status_file: Path, status_filter: StatusType, language: str = "ja") -> None:
       """List files with a specific translation status."""
       status_data = load_status_file(status_file)

       matching_files = []

       for file_key, file_data in status_data["translations"].items():
           trans_data = file_data.get("translations", {}).get(language, {})
           if trans_data.get("status", "not_started") == status_filter:
               matching_files.append(file_key)

       console.print(f"\n[bold]Files with status '{status_filter}' for language '{language}':[/bold]")

       if not matching_files:
           console.print("[yellow]No files found with this status.[/yellow]")
       else:
           for file_path in sorted(matching_files):
               console.print(f"  - {file_path}")

           console.print(f"\nTotal: {len(matching_files)} files")
   ```

2. Update the main() function:

   ```python
   elif args.command == "list":
       list_files_by_status(Path("translations-status.yml"), args.status)
   ```

**Success Criteria**:

- Command lists files filtered by status
- Output is sorted and shows total count

## Phase 3: Add Validation Features

### Task 3.1: Implement Front Matter Validation

**Description**: Add validation to check front matter consistency in translated files.

**Steps**:

1. Add this validation function:

   ```python
   def validate_front_matter(source_path: Path, target_path: Path) -> List[str]:
       """
       Validate front matter consistency between source and target files.

       Returns:
           List of validation errors (empty if valid)
       """
       errors = []

       try:
           with open(source_path, 'r', encoding='utf-8') as f:
               source_meta = frontmatter.load(f).metadata

           with open(target_path, 'r', encoding='utf-8') as f:
               target_meta = frontmatter.load(f).metadata

           # Check required fields
           if source_meta.get("id") != target_meta.get("id"):
               errors.append(f"ID mismatch: '{source_meta.get('id')}' vs '{target_meta.get('id')}'")

           if source_meta.get("type") != target_meta.get("type"):
               errors.append(f"Type mismatch: '{source_meta.get('type')}' vs '{target_meta.get('type')}'")

           # Check translation links
           if "translations" not in target_meta:
               errors.append("Missing 'translations' field in target file")

           if "translation_of" not in target_meta:
               errors.append("Missing 'translation_of' field in target file")

       except Exception as e:
           errors.append(f"Error reading files: {e}")

       return errors
   ```

2. Add the validate command implementation:

   ```python
   def validate_translations(base_path: Path, status_file: Path) -> None:
       """Validate all translations for consistency."""
       status_data = load_status_file(status_file)
       source_lang = status_data["metadata"]["source_language"]

       total_errors = 0

       console.print("[bold blue]Validating translations...[/bold blue]\n")

       for file_key, file_data in status_data["translations"].items():
           source_path = base_path / source_lang / file_key

           for lang, trans_data in file_data.get("translations", {}).items():
               if trans_data.get("status") in ["completed", "needs_update"]:
                   target_path = base_path / lang / file_key

                   if target_path.exists():
                       errors = validate_front_matter(source_path, target_path)

                       if errors:
                           total_errors += len(errors)
                           console.print(f"[red]❌ {file_key} ({lang}):[/red]")
                           for error in errors:
                               console.print(f"   - {error}")

       if total_errors == 0:
           console.print("[green] All translations are valid![/green]")
       else:
           console.print(f"\n[red]Found {total_errors} validation errors.[/red]")
   ```

**Success Criteria**:

- Validation catches missing or mismatched metadata
- Clear error messages for each issue

### Task 3.2: Implement Statistics Command

**Description**: Add detailed statistics about translation progress.

**Steps**:

1. Add this function:

   ```python
   def show_statistics(status_file: Path) -> None:
       """Show detailed translation statistics."""
       status_data = load_status_file(status_file)

       # Create statistics table
       table = Table(title="Translation Statistics by Domain")
       table.add_column("Domain", style="cyan")

       for lang in status_data["metadata"]["target_languages"]:
           table.add_column(f"{lang.upper()}", justify="center")

       # Organize by domain
       domains = {}
       for file_key in status_data["translations"]:
           domain = file_key.split('/')[0] if '/' in file_key else 'root'
           if domain not in domains:
               domains[domain] = {lang: {"total": 0, "completed": 0}
                                 for lang in status_data["metadata"]["target_languages"]}

           for lang in status_data["metadata"]["target_languages"]:
               domains[domain][lang]["total"] += 1
               trans_status = status_data["translations"][file_key].get("translations", {}).get(lang, {}).get("status")
               if trans_status == "completed":
                   domains[domain][lang]["completed"] += 1

       # Add rows to table
       for domain in sorted(domains.keys()):
           row = [domain]
           for lang in status_data["metadata"]["target_languages"]:
               stats = domains[domain][lang]
               percentage = (stats["completed"] / stats["total"] * 100) if stats["total"] > 0 else 0
               row.append(f"{stats['completed']}/{stats['total']} ({percentage:.0f}%)")
           table.add_row(*row)

       console.print(table)
   ```

2. Update the main() function to call this for the stats command.

**Success Criteria**:

- Statistics show domain-by-domain breakdown
- Percentages are calculated correctly

## Phase 4: Integration with Build Pipeline

### Task 4.1: Create RDF Integration Module

**Description**: Create a module to add translation edges to the RDF graph.

**Steps**:

1. Create file `scripts/translation_graph.py`:

   ```python
   """
   Integration module for adding translation relationships to the RDF graph.
   """

   from pathlib import Path
   from rdflib import Graph, Namespace, URIRef, Literal
   from rdflib.namespace import RDF, RDFS

   # Define namespaces
   MATH = Namespace("http://modernmath.org/ontology#")


   def add_translation_edges(graph: Graph, status_file: Path) -> None:
       """
       Add translation relationships to the RDF graph.

       Args:
           graph: RDF graph to modify
           status_file: Path to translations-status.yml
       """
       import yaml

       with open(status_file, 'r') as f:
           status_data = yaml.safe_load(f)

       # Add translation predicate if not exists
       graph.add((MATH.hasTranslation, RDF.type, RDF.Property))
       graph.add((MATH.hasTranslation, RDFS.label, Literal("has translation")))

       # Add edges for each translation
       for file_key, file_data in status_data["translations"].items():
           # Extract concept ID from file path (e.g., "algebra/def-group.qmd" -> "group")
           concept_id = Path(file_key).stem.replace("def-", "").replace("thm-", "").replace("ex-", "")
           source_uri = URIRef(f"http://modernmath.org/concepts/{concept_id}")

           for lang, trans_data in file_data.get("translations", {}).items():
               if trans_data.get("status") == "completed":
                   trans_uri = URIRef(f"http://modernmath.org/concepts/{concept_id}_{lang}")
                   graph.add((source_uri, MATH.hasTranslation, trans_uri))
                   graph.add((trans_uri, MATH.language, Literal(lang)))
   ```

2. Modify `scripts/build_graph.py` to import and use this function (add at the end of the build process).

**Success Criteria**:

- Module imports without errors
- Translation edges are added to the RDF graph

### Task 4.2: Add Status Badges to Templates

**Description**: Create Quarto partial templates for translation status badges.

**Steps**:

1. Create file `_extensions/translation-status/_extension.yml`:

   ```yaml
   title: Translation Status
   author: ModernMath Team
   version: 1.0.0
   quarto-required: ">=1.3.0"
   contributes:
     shortcodes:
       - translation-status.lua
   ```

2. Create file `_extensions/translation-status/translation-status.lua`:

   ```lua
   -- Quarto extension for translation status badges

   function translation_status(args)
     local status = pandoc.utils.stringify(args[1])
     local badge_html = ""

     if status == "completed" then
       badge_html = '<span class="badge bg-success">Translated</span>'
     elseif status == "needs_update" then
       badge_html = '<span class="badge bg-warning">Needs Update</span>'
     elseif status == "in_progress" then
       badge_html = '<span class="badge bg-info">In Progress</span>'
     else
       badge_html = '<span class="badge bg-secondary">Not Translated</span>'
     end

     return pandoc.RawInline('html', badge_html)
   end
   ```

3. Test by adding `{{< translation-status completed >}}` to any .qmd file.

**Success Criteria**:

- Badge displays correctly in rendered HTML
- Different statuses show different colors

## Phase 5: CI/CD Integration

### Task 5.1: Create GitHub Actions Workflow

**Description**: Add translation validation to CI/CD pipeline.

**Steps**:

1. Create file `.github/workflows/translation-check.yml`:

   ```yaml
   name: Translation Status Check

   on:
     push:
       paths:
         - "content/**/*.qmd"
         - "translations-status.yml"
     pull_request:
       paths:
         - "content/**/*.qmd"

   jobs:
     check-translations:
       runs-on: ubuntu-latest

       steps:
         - uses: actions/checkout@v4

         - name: Set up Python
           uses: actions/setup-python@v4
           with:
             python-version: "3.11"

         - name: Install Poetry
           uses: snok/install-poetry@v1

         - name: Install dependencies
           run: poetry install

         - name: Update translation status
           run: poetry run python scripts/manage_translations.py update

         - name: Validate translations
           run: poetry run python scripts/manage_translations.py validate

         - name: Generate report
           run: poetry run python scripts/manage_translations.py report

         - name: Check for uncommitted changes
           run: |
             if [[ -n $(git status -s translations-status.yml) ]]; then
               echo "Translation status file needs to be updated!"
               echo "Run 'poetry run python scripts/manage_translations.py update' locally"
               exit 1
             fi
   ```

2. Test by creating a pull request that adds or modifies a content file.

**Success Criteria**:

- Workflow runs on content changes
- Fails if translation status is outdated

### Task 5.2: Add Pre-commit Hook

**Description**: Create a pre-commit hook to update translation status.

**Steps**:

1. Create file `.pre-commit-config.yaml`:

   ```yaml
   repos:
     - repo: local
       hooks:
         - id: update-translation-status
           name: Update translation status
           entry: poetry run python scripts/manage_translations.py update
           language: system
           files: 'content/.*\.qmd$'
           pass_filenames: false
   ```

2. Install pre-commit: `poetry add --group dev pre-commit`
3. Set up hooks: `poetry run pre-commit install`

**Success Criteria**:

- Hook runs before commits affecting content files
- Translation status is automatically updated

## Phase 6: Documentation and Testing

### Task 6.1: Add Script Documentation

**Description**: Add comprehensive documentation to the management script.

**Steps**:

1. Add docstrings to all functions following Google style
2. Add a README section in `scripts/README.md` explaining the translation system
3. Add usage examples for each command

**Success Criteria**:

- All functions have complete docstrings
- README includes examples for all commands

### Task 6.2: Create Unit Tests

**Description**: Add tests for the translation management system.

**Steps**:

1. Create file `tests/test_translation_management.py`
2. Add tests for:
   - File hash calculation
   - Status detection logic
   - Front matter validation
   - Report generation

**Success Criteria**:

- All core functions have tests
- Tests pass with `poetry run pytest tests/test_translation_management.py`

## Completion Checklist

- [ ] Phase 1: Core Infrastructure Setup
  - [ ] Task 1.1: Create status file structure
  - [ ] Task 1.2: Set up project configuration
- [ ] Phase 2: Create Management Script
  - [ ] Task 2.1: Create basic script structure
  - [ ] Task 2.2: Implement file scanning
  - [ ] Task 2.3: Implement update command
  - [ ] Task 2.4: Implement report command
  - [ ] Task 2.5: Implement list command
- [ ] Phase 3: Add Validation Features
  - [ ] Task 3.1: Implement front matter validation
  - [ ] Task 3.2: Implement statistics command
- [ ] Phase 4: Integration with Build Pipeline
  - [ ] Task 4.1: Create RDF integration module
  - [ ] Task 4.2: Add status badges to templates
- [ ] Phase 5: CI/CD Integration
  - [ ] Task 5.1: Create GitHub Actions workflow
  - [ ] Task 5.2: Add pre-commit hook
- [ ] Phase 6: Documentation and Testing
  - [ ] Task 6.1: Add script documentation
  - [ ] Task 6.2: Create unit tests

## Notes for Junior Engineers

1. **Always test locally** before committing changes
2. **Use virtual environment**: Always run commands with `poetry run`
3. **Check YAML syntax**: Use online YAML validators if unsure
4. **Ask questions**: If any step is unclear, ask for clarification
5. **Commit frequently**: Make small, focused commits for each task
6. **Read error messages**: Python errors usually point to the exact problem
7. **Use type hints**: They help catch errors early and make code clearer

## Dependencies to Install

Before starting, ensure these are in pyproject.toml:

```toml
[tool.poetry.dependencies]
python = "^3.11"
pyyaml = "^6.0"
python-frontmatter = "^1.0.0"
rich = "^13.0.0"

[tool.poetry.group.dev.dependencies]
pytest = "^7.0.0"
pre-commit = "^3.0.0"
```

Run `poetry install` after adding these dependencies.
