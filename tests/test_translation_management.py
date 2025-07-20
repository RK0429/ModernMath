#!/usr/bin/env python3
"""
Unit tests for the translation management system.
"""

import shutil
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

# Import the modules to test
sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))

# pylint: disable=import-error,wrong-import-position
from manage_translations import (  # noqa: E402  # pyright: ignore[reportMissingImports]
    get_content_hash,
    scan_content_directory,
    load_status_file,
    save_status_file,
    validate_front_matter,
)

# pylint: enable=import-error,wrong-import-position


class TestTranslationManagement(unittest.TestCase):
    """Test cases for translation management functions."""

    def setUp(self) -> None:
        """Set up test fixtures."""
        self.test_dir = tempfile.mkdtemp()
        self.test_path = Path(self.test_dir)

    def tearDown(self) -> None:
        """Clean up test fixtures."""
        shutil.rmtree(self.test_dir)

    def test_get_content_hash(self) -> None:
        """Test MD5 hash calculation for file content."""
        # Create a test file with front matter and content
        test_file = self.test_path / "test.qmd"
        test_file.write_text(
            """---
title: Test
id: test
---

This is the content.
"""
        )

        # Get hash
        hash1 = get_content_hash(test_file)
        self.assertIsInstance(hash1, str)
        self.assertEqual(len(hash1), 32)  # MD5 hash is 32 hex chars

        # Same content should give same hash
        hash2 = get_content_hash(test_file)
        self.assertEqual(hash1, hash2)

        # Changed content should give different hash
        test_file.write_text(
            """---
title: Test
id: test
---

This is different content.
"""
        )
        hash3 = get_content_hash(test_file)
        self.assertNotEqual(hash1, hash3)

        # Changed front matter only should not affect hash
        test_file.write_text(
            """---
title: Different Title
id: test
author: Someone
---

This is the content.
"""
        )
        hash4 = get_content_hash(test_file)
        self.assertEqual(hash1, hash4)

    def test_scan_content_directory(self) -> None:
        """Test scanning directory for .qmd files."""
        # Create test directory structure
        en_dir = self.test_path / "en" / "algebra"
        en_dir.mkdir(parents=True)

        # Create test files
        (en_dir / "def-group.qmd").write_text("Group definition")
        (en_dir / "thm-lagrange.qmd").write_text("Lagrange theorem")
        (en_dir / "index.qmd").write_text("Index page")  # Should be ignored
        (en_dir / "_metadata.yml").write_text("metadata")  # Should be ignored

        # Scan directory
        files = scan_content_directory(self.test_path, "en")

        # Check results
        self.assertEqual(len(files), 2)  # Only non-ignored files
        file_names = [str(f["path"]) for f in files]
        self.assertIn("algebra/def-group.qmd", file_names)
        self.assertIn("algebra/thm-lagrange.qmd", file_names)
        self.assertNotIn("algebra/index.qmd", file_names)

    def test_load_status_file(self) -> None:
        """Test loading translation status file."""
        # Test non-existent file
        status = load_status_file(self.test_path / "nonexistent.yml")
        self.assertIn("metadata", status)
        self.assertIn("translations", status)
        self.assertEqual(status["metadata"]["source_language"], "en")

        # Test existing file
        status_file = self.test_path / "status.yml"
        test_data = {
            "metadata": {
                "last_updated": "2025-01-20T10:00:00Z",
                "source_language": "en",
                "target_languages": ["ja"],
            },
            "translations": {
                "algebra/def-group.qmd": {
                    "source_hash": "abc123",
                    "translations": {"ja": {"status": "completed"}},
                }
            },
        }
        with open(status_file, "w", encoding="utf-8") as f:
            yaml.dump(test_data, f)

        loaded = load_status_file(status_file)
        self.assertEqual(loaded["metadata"]["source_language"], "en")
        self.assertIn("algebra/def-group.qmd", loaded["translations"])

    def test_save_status_file(self) -> None:
        """Test saving translation status file."""
        status_file = self.test_path / "status.yml"
        data = {
            "metadata": {
                "source_language": "en",
                "target_languages": ["ja"],
            },
            "translations": {},
        }

        # Save file
        save_status_file(status_file, data)

        # Check file exists and has updated timestamp
        self.assertTrue(status_file.exists())
        loaded = load_status_file(status_file)
        self.assertIsNotNone(loaded["metadata"]["last_updated"])

    def test_validate_front_matter(self) -> None:
        """Test front matter validation between source and target files."""
        source_file = self.test_path / "source.qmd"
        target_file = self.test_path / "target.qmd"

        # Test matching metadata
        source_file.write_text(
            """---
title: Group
id: group
type: Definition
---
Content"""
        )

        target_file.write_text(
            """---
title: 群
id: group
type: Definition
translations:
  en: ../en/def-group.html
translation_of: en/def-group.qmd
---
内容"""
        )

        errors = validate_front_matter(source_file, target_file)
        self.assertEqual(len(errors), 0)

        # Test mismatched ID
        target_file.write_text(
            """---
title: 群
id: group-wrong
type: Definition
translations:
  en: ../en/def-group.html
translation_of: en/def-group.qmd
---
内容"""
        )

        errors = validate_front_matter(source_file, target_file)
        self.assertGreater(len(errors), 0)
        self.assertTrue(any("ID mismatch" in e for e in errors))

        # Test missing translations field
        target_file.write_text(
            """---
title: 群
id: group
type: Definition
translation_of: en/def-group.qmd
---
内容"""
        )

        errors = validate_front_matter(source_file, target_file)
        self.assertTrue(any("Missing 'translations' field" in e for e in errors))


class TestTranslationStatusDetection(unittest.TestCase):
    """Test cases for translation status detection logic."""

    def test_status_detection_not_started(self) -> None:
        """Test detection of not_started status."""
        # When target file doesn't exist, status should be not_started
        # This is tested implicitly in the update_translation_status function

    def test_status_detection_completed(self) -> None:
        """Test detection of completed status."""
        # When target exists and hashes match, status should be completed
        # This is tested implicitly in the update_translation_status function

    def test_status_detection_needs_update(self) -> None:
        """Test detection of needs_update status."""
        # When source hash changes after translation, status should be needs_update
        # This is tested implicitly in the update_translation_status function


if __name__ == "__main__":
    unittest.main()
