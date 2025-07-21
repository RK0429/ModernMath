#!/usr/bin/env python3
"""
Translation management system for ModernMath Knowledge Graph Wiki.
Tracks and manages translation status between languages.
"""

import argparse
import copy
import hashlib
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Literal, Any

import yaml
import frontmatter
from rich.console import Console
from rich.table import Table

# Initialize console for pretty output
console = Console()

# Type definitions
StatusType = Literal["not_started", "in_progress", "completed", "needs_update"]


def get_content_hash(file_path: Path) -> str:
    """
    Calculate MD5 hash of file content (excluding front matter).

    Args:
        file_path: Path to the content file

    Returns:
        MD5 hash string
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)
            # Hash only the content, not the metadata
            content = post.content.strip()
            return hashlib.md5(content.encode("utf-8")).hexdigest()
    except (IOError, OSError) as e:
        console.print(f"[red]Error hashing {file_path}: {e}[/red]")
        return ""


def scan_content_directory(base_path: Path, language: str) -> List[Dict[str, Any]]:
    """
    Scan a language directory for all .qmd files.

    Args:
        base_path: Base content directory path
        language: Language code (e.g., 'en', 'ja')

    Returns:
        List of dictionaries with file information
    """
    content_dir = base_path / language
    files: List[Dict[str, Any]] = []

    if not content_dir.exists():
        console.print(f"[red]Directory not found: {content_dir}[/red]")
        return files

    # Find all .qmd files
    for qmd_file in content_dir.rglob("*.qmd"):
        # Skip ignored patterns
        relative_path = qmd_file.relative_to(content_dir)

        # Skip index files and metadata files
        if (
            qmd_file.name == "index.qmd"
            or qmd_file.name == "_metadata.yml"
            or "_extensions" in str(relative_path)
        ):
            continue

        files.append(
            {
                "path": relative_path,
                "full_path": qmd_file,
                "hash": get_content_hash(qmd_file),
                "language": language,
            }
        )

    return files


def load_status_file(status_file: Path) -> Dict[str, Any]:
    """Load the translation status YAML file."""
    if not status_file.exists():
        return {
            "metadata": {"last_updated": None, "source_language": "en", "target_languages": ["ja"]},
            "translations": {},
        }

    with open(status_file, "r", encoding="utf-8") as f:
        return yaml.safe_load(f) or {}


def save_status_file(
    status_file: Path, data: Dict[str, Any], update_timestamp: bool = True
) -> None:
    """Save the translation status YAML file."""
    if update_timestamp:
        data["metadata"]["last_updated"] = datetime.now(timezone.utc).isoformat()

    with open(status_file, "w", encoding="utf-8") as f:
        yaml.dump(data, f, default_flow_style=False, sort_keys=False)


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
    # Create a deep copy to compare later
    original_data = copy.deepcopy(status_data)

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
                "translations": {},
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
                # Determine status
                if trans_info.get("status") == "completed":
                    # Check if source has changed
                    if trans_info.get("translated_hash") != source_file["hash"]:
                        trans_info["status"] = "needs_update"
                elif trans_info.get("status") != "in_progress":
                    # Assume completed if file exists and not marked otherwise
                    # Only update if status is actually changing
                    if trans_info.get("status") != "completed":
                        trans_info["status"] = "completed"
                        trans_info["translated_hash"] = source_file["hash"]
                        trans_info["translated_at"] = datetime.now(timezone.utc).isoformat()
            else:
                # Translation doesn't exist
                if trans_info.get("status") != "not_started":
                    trans_info["status"] = "not_started"

    # Only save if there are actual changes (excluding the timestamp)
    # Remove timestamps for comparison
    def remove_timestamps(data: Dict[str, Any]) -> Dict[str, Any]:
        data_copy = copy.deepcopy(data)
        if "metadata" in data_copy and "last_updated" in data_copy["metadata"]:
            del data_copy["metadata"]["last_updated"]
        return data_copy

    # Check if there are any actual changes
    original_without_timestamp = remove_timestamps(original_data)
    current_without_timestamp = remove_timestamps(status_data)

    if original_without_timestamp != current_without_timestamp:
        # There are actual changes, save with updated timestamp
        save_status_file(status_file, status_data, update_timestamp=True)
        console.print("[green]Translation status updated successfully![/green]")
    else:
        # No changes, skip saving to avoid timestamp update
        console.print("[yellow]No changes detected in translation status.[/yellow]")


def generate_report(status_file: Path, report_format: str = "summary") -> None:
    """Generate translation status report."""
    status_data = load_status_file(status_file)

    if report_format == "summary":
        # Count statistics
        stats = {
            lang: {"completed": 0, "in_progress": 0, "needs_update": 0, "not_started": 0}
            for lang in status_data["metadata"]["target_languages"]
        }

        total_files = len(status_data["translations"])

        for file_data in status_data["translations"].values():
            for lang, trans_data in file_data.get("translations", {}).items():
                status = trans_data.get("status", "not_started")
                stats[lang][status] += 1

        # Print summary
        console.print("\n[bold]Translation Status Summary[/bold]")
        console.print("=" * 40)
        console.print(f"Total source files: {total_files}")
        source_lang = status_data["metadata"]["source_language"]
        target_langs = ", ".join(status_data["metadata"]["target_languages"])
        console.print(f"Languages: {source_lang} (source) → {target_langs}")

        for lang, lang_stats in stats.items():
            console.print(f"\n[bold]{lang.upper()}:[/bold]")
            total = sum(lang_stats.values())
            for status, count in lang_stats.items():
                percentage = (count / total * 100) if total > 0 else 0
                console.print(f"- {status.replace('_', ' ').title()}: {count} ({percentage:.1f}%)")


def list_files_by_status(
    status_file: Path, status_filter: StatusType, language: str = "ja"
) -> None:
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


def validate_front_matter(source_path: Path, target_path: Path) -> List[str]:
    """
    Validate front matter consistency between source and target files.

    Returns:
        List of validation errors (empty if valid)
    """
    errors = []

    try:
        with open(source_path, "r", encoding="utf-8") as f:
            source_meta = frontmatter.load(f).metadata

        with open(target_path, "r", encoding="utf-8") as f:
            target_meta = frontmatter.load(f).metadata

        # Check required fields
        if source_meta.get("id") != target_meta.get("id"):
            errors.append(f"ID mismatch: '{source_meta.get('id')}' vs '{target_meta.get('id')}'")

        if source_meta.get("type") != target_meta.get("type"):
            errors.append(
                f"Type mismatch: '{source_meta.get('type')}' vs '{target_meta.get('type')}'"
            )

        # Check translation links
        if "translations" not in target_meta:
            errors.append("Missing 'translations' field in target file")

        if "translation_of" not in target_meta:
            errors.append("Missing 'translation_of' field in target file")

    except (IOError, OSError) as e:
        errors.append(f"Error reading files: {e}")

    return errors


def validate_translations(base_path: Path, status_file: Path) -> None:
    """Validate all translations for consistency."""
    status_data = load_status_file(status_file)
    source_lang = status_data["metadata"]["source_language"]

    total_errors = 0

    console.print("[bold blue]Validating translations...[/bold blue]\n")

    for file_key, file_data in status_data["translations"].items():
        source_path = base_path / source_lang / file_key
        total_errors += _validate_file_translations(file_key, file_data, source_path, base_path)

    if total_errors == 0:
        console.print("[green]✅ All translations are valid![/green]")
    else:
        console.print(f"\n[red]Found {total_errors} validation errors.[/red]")


def _validate_file_translations(
    file_key: str, file_data: Dict[str, Any], source_path: Path, base_path: Path
) -> int:
    """Validate translations for a single file."""
    errors_count = 0

    for lang, trans_data in file_data.get("translations", {}).items():
        if trans_data.get("status") not in ["completed", "needs_update"]:
            continue

        target_path = base_path / lang / file_key
        if not target_path.exists():
            continue

        errors = validate_front_matter(source_path, target_path)
        if errors:
            errors_count += len(errors)
            console.print(f"[red]❌ {file_key} ({lang}):[/red]")
            for error in errors:
                console.print(f"   - {error}")

    return errors_count


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
        domain = file_key.split("/")[0] if "/" in file_key else "root"
        if domain not in domains:
            domains[domain] = {
                lang: {"total": 0, "completed": 0}
                for lang in status_data["metadata"]["target_languages"]
            }

        for lang in status_data["metadata"]["target_languages"]:
            domains[domain][lang]["total"] += 1
            trans_status = (
                status_data["translations"][file_key]
                .get("translations", {})
                .get(lang, {})
                .get("status")
            )
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


def main() -> None:
    """Main entry point for the translation management system."""
    parser = argparse.ArgumentParser(description="Manage translations for ModernMath content")

    subparsers = parser.add_subparsers(dest="command", help="Available commands")

    # Add subcommands
    subparsers.add_parser("update", help="Update translation status")
    subparsers.add_parser("report", help="Generate translation report")

    list_parser = subparsers.add_parser("list", help="List files by status")
    list_parser.add_argument(
        "--status",
        choices=["not_started", "in_progress", "completed", "needs_update"],
        required=True,
        help="Filter by translation status",
    )

    subparsers.add_parser("validate", help="Validate all translations")
    subparsers.add_parser("stats", help="Show translation statistics")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        sys.exit(1)

    # Command routing
    if args.command == "update":
        update_translation_status(Path("content"), Path("translations-status.yml"))
    elif args.command == "report":
        generate_report(Path("translations-status.yml"))
    elif args.command == "list":
        list_files_by_status(Path("translations-status.yml"), args.status)
    elif args.command == "validate":
        validate_translations(Path("content"), Path("translations-status.yml"))
    elif args.command == "stats":
        show_statistics(Path("translations-status.yml"))


if __name__ == "__main__":
    main()
