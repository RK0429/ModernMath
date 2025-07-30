#!/usr/bin/env python3
"""
Validate Lean proofs in the formal/ directory.

This script runs `lake build` to ensure all Lean proofs compile correctly.
It returns 0 if successful, 1 if there are errors.
"""

import shutil
import subprocess
import sys
from pathlib import Path

# Find project root
SCRIPT_DIR = Path(__file__).parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent
FORMAL_DIR = PROJECT_ROOT / "formal"


def check_lean_installed() -> bool:
    """Check if Lean and Lake are installed."""
    if not shutil.which("lake"):
        print("Error: Lake (Lean's build system) is not installed or not in PATH")
        print("Please install Lean 4: https://leanprover.github.io/lean4/doc/quickstart.html")
        return False
    return True


def validate_lean_proofs() -> bool:
    """Run lake build to validate all Lean proofs."""
    if not check_lean_installed():
        return False

    if not FORMAL_DIR.exists():
        print(f"Warning: Formal proofs directory not found at {FORMAL_DIR}")
        return True  # Not an error if directory doesn't exist

    print(f"Validating Lean proofs in {FORMAL_DIR}...")

    try:
        # Run lake build (Lake will automatically select an appropriate
        # level of parallelism. Recent versions of Lake have removed the
        # short `-j`/`--jobs` option, so we avoid passing it here.)

        result = subprocess.run(
            ["lake", "build"],
            cwd=FORMAL_DIR,
            capture_output=True,
            text=True,
            check=False,
        )

        # Print output for debugging
        if result.stdout:
            print(result.stdout)

        if result.returncode != 0:
            print("\n❌ Lean proof validation failed!")
            if result.stderr:
                print("Errors:")
                print(result.stderr)
            return False

        # Check for warnings (especially 'sorry' usage)
        if "warning" in result.stdout.lower():
            print("\n⚠️  Warnings found in Lean proofs:")
            # Extract warning lines
            for line in result.stdout.split("\n"):
                if "warning" in line.lower():
                    print(f"  {line.strip()}")
            print("\nConsider completing proofs marked with 'sorry'")

        print("\n✅ Lean proof validation successful!")
        return True

    except subprocess.SubprocessError as e:
        print(f"Error running lake build: {e}")
        return False
    except OSError as e:
        print(f"Error accessing lake command or directory: {e}")
        return False


def main() -> None:
    """Main entry point."""
    if validate_lean_proofs():
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
