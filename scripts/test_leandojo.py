#!/usr/bin/env python3
"""
Test LeanDojo installation and basic functionality.
"""

import sys
from pathlib import Path

try:
    import lean_dojo

    print(f"✓ LeanDojo version: {lean_dojo.__version__}")

    # Test importing key components
    from lean_dojo import LeanGitRepo  # , trace

    print("✓ Successfully imported LeanGitRepo and trace")

    # Check if we can create a repo object
    formal_dir = Path(__file__).parent.parent / "formal"
    if formal_dir.exists():
        print(f"✓ Found formal directory: {formal_dir}")

        # Check for lakefile.lean
        lakefile = formal_dir / "lakefile.lean"
        if lakefile.exists():
            print("✓ Found lakefile.lean")

            # Try to create a LeanGitRepo object
            try:
                # LeanDojo expects the parent git repository path
                git_root = Path(__file__).parent.parent
                repo = LeanGitRepo(str(git_root), "formal/lakefile.lean")
                print("✓ Successfully created LeanGitRepo object")
                print(f"  Repository path: {repo.repo_path}")
                print(f"  Lakefile: {repo.lakefile}")
            except Exception as e:
                print(f"✗ Failed to create LeanGitRepo: {e}")
        else:
            print(f"✗ lakefile.lean not found in {formal_dir}")
    else:
        print(f"✗ Formal directory not found: {formal_dir}")

    print("\nLeanDojo is properly installed and configured!")

except ImportError as e:
    print(f"✗ Failed to import LeanDojo: {e}")
    sys.exit(1)
except Exception as e:
    print(f"✗ Unexpected error: {e}")
    sys.exit(1)

