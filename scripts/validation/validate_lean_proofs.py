#!/usr/bin/env python3
"""
Validate Lean proofs in the formal/ directory - Improved version.

This script runs `lake build` to ensure all Lean proofs compile correctly.
It returns 0 if successful, 1 if there are errors.
"""

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, Any, List, Tuple

# Find project root
SCRIPT_DIR = Path(__file__).parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent
FORMAL_DIR = PROJECT_ROOT / "formal"
VALIDATION_RESULTS_PATH = PROJECT_ROOT / "lean_validation_results.json"


def check_lean_installed() -> bool:
    """Check if Lean and Lake are installed."""
    if not shutil.which("lake"):
        print("Error: Lake (Lean's build system) is not installed or not in PATH")
        print("Please install Lean 4: https://leanprover.github.io/lean4/doc/quickstart.html")
        return False
    return True


def parse_lake_output_v2(  # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    output: str,
) -> Dict[str, Dict[str, Any]]:
    """Parse Lake build output to extract status for each module - Improved version.

    Returns a dict mapping module names to their validation status.
    """
    module_status: Dict[str, Dict[str, Any]] = {}

    # Regular expressions for parsing the new Lake output format
    # ✓/✅ = success, ⚠ = warning, ✖ = error
    module_re = re.compile(r"[\u2713\u2705\u26a0\u2716]\s*\[(\d+)/(\d+)\]\s+(\w+)\s+(\S+)")
    error_re = re.compile(r"error:\s*(\S+?)(?:\.lean)?:(\d+):(\d+):\s*(.+)")
    warning_re = re.compile(r"warning:\s*(\S+?)(?:\.lean)?:(\d+):(\d+):\s*(.+)")
    sorry_re = re.compile(r"declaration uses 'sorry'")

    lines = output.split("\n")
    current_module = None

    for line in lines:
        # Check for module status line
        module_match = module_re.search(line)
        if module_match:
            status_icon = line[0]  # First character is the status icon
            # action = module_match.group(3)  # Building, Built, Replayed (unused)
            module_name = module_match.group(4)

            if module_name not in module_status:
                module_status[module_name] = {
                    "status": "not_implemented",
                    "errors": [],
                    "warnings": [],
                    "has_sorry": False,
                }

            # Determine status based on icon and action
            if status_icon in ["✓", "✅"]:
                module_status[module_name]["status"] = "completed"
            elif status_icon == "⚠":
                module_status[module_name]["status"] = "warnings_present"
            elif status_icon == "✖":
                module_status[module_name]["status"] = "errors_present"

            current_module = module_name

        # Check for errors
        error_match = error_re.search(line)
        if error_match:
            file_path = error_match.group(1)
            line_num = error_match.group(2)
            col_num = error_match.group(3)
            message = error_match.group(4)

            # Find the module this error belongs to
            module_found = False
            for module_name, module_info in module_status.items():
                module_path = module_name.replace(".", "/")
                if module_path in file_path or file_path.endswith(f"{module_path}.lean"):
                    module_info["errors"].append(
                        {"file": file_path, "line": line_num, "column": col_num, "message": message}
                    )
                    module_info["status"] = "errors_present"
                    module_found = True
                    break

            # If not found by path, use current module
            if not module_found and current_module and current_module in module_status:
                module_status[current_module]["errors"].append(
                    {"file": file_path, "line": line_num, "column": col_num, "message": message}
                )
                module_status[current_module]["status"] = "errors_present"

        # Check for warnings
        warning_match = warning_re.search(line)
        if warning_match:
            file_path = warning_match.group(1)
            line_num = warning_match.group(2)
            col_num = warning_match.group(3)
            message = warning_match.group(4)

            # Check if it's a 'sorry' warning
            is_sorry = sorry_re.search(message)

            # Find the module this warning belongs to
            module_found = False
            for module_name, module_info in module_status.items():
                module_path = module_name.replace(".", "/")
                if module_path in file_path or file_path.endswith(f"{module_path}.lean"):
                    if is_sorry:
                        module_info["has_sorry"] = True

                    module_info["warnings"].append(
                        {"file": file_path, "line": line_num, "column": col_num, "message": message}
                    )
                    # Only update status if not already marked as error
                    if module_info["status"] not in ["errors_present"]:
                        module_info["status"] = "warnings_present"
                    module_found = True
                    break

            # If not found by path, use current module
            if not module_found and current_module and current_module in module_status:
                if is_sorry:
                    module_status[current_module]["has_sorry"] = True

                module_status[current_module]["warnings"].append(
                    {"file": file_path, "line": line_num, "column": col_num, "message": message}
                )
                if module_status[current_module]["status"] not in ["errors_present"]:
                    module_status[current_module]["status"] = "warnings_present"

    return module_status


def get_lean_modules() -> List[Tuple[str, Path]]:
    """Get all Lean modules in the formal directory.

    Returns list of (module_name, file_path) tuples.
    """
    modules: List[Tuple[str, Path]] = []
    if not FORMAL_DIR.exists():
        return modules

    for lean_file in FORMAL_DIR.rglob("*.lean"):
        # Skip lakefile.lean and other special files
        if lean_file.name in ["lakefile.lean", "lean-toolchain"]:
            continue

        # Convert path to module name
        relative_path = lean_file.relative_to(FORMAL_DIR)
        module_name = str(relative_path.with_suffix("")).replace("/", ".")
        modules.append((module_name, lean_file))

    return modules


def load_lean_mappings() -> Dict[str, Any]:
    """Load Lean mappings to get node ID associations."""
    mappings_path = PROJECT_ROOT / "lean_mappings.json"
    if not mappings_path.exists():
        return {}

    try:
        with open(mappings_path, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except (IOError, json.JSONDecodeError):
        return {}


def validate_lean_proofs() -> (
    bool
):  # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    """Run lake build to validate all Lean proofs."""
    if not check_lean_installed():
        return False

    if not FORMAL_DIR.exists():
        print(f"Warning: Formal proofs directory not found at {FORMAL_DIR}")
        return True  # Not an error if directory doesn't exist

    print(f"Validating Lean proofs in {FORMAL_DIR}...")

    # Get all Lean modules
    lean_modules = get_lean_modules()

    # Initialize validation results
    validation_results: Dict[str, Any] = {
        "modules": {},
        "summary": {
            "total": 0,
            "not_implemented": 0,
            "errors_present": 0,
            "warnings_present": 0,
            "completed": 0,
        },
    }

    # Load Lean mappings to associate modules with node IDs
    lean_mappings = load_lean_mappings()
    module_to_node: Dict[str, str] = {}
    if "node_to_lean" in lean_mappings:
        for node_id, lean_data in lean_mappings["node_to_lean"].items():
            if "module_name" in lean_data:
                module_to_node[lean_data["module_name"]] = node_id

    try:
        # Run lake build
        print("Running lake build...")
        result = subprocess.run(
            ["lake", "build"],
            cwd=FORMAL_DIR,
            capture_output=True,
            text=True,
            check=False,
        )

        # Parse the output
        all_output = result.stdout + "\n" + result.stderr
        module_status = parse_lake_output_v2(all_output)

        # Process each module
        for module_name, module_path in lean_modules:
            if module_name in module_status:
                status_info: Dict[str, Any] = module_status[module_name]
            else:
                # Module wasn't mentioned in build output, check if file has content
                try:
                    with open(module_path, "r", encoding="utf-8") as f:
                        content = f.read().strip()
                        # Check if file has actual proof content (not just imports)
                        has_content = any(
                            line.strip()
                            and not line.strip().startswith("import")
                            and not line.strip().startswith("--")
                            for line in content.split("\n")
                        )

                        if not has_content:
                            status_info = {
                                "status": "not_implemented",
                                "errors": [],
                                "warnings": [],
                                "has_sorry": False,
                            }
                        else:
                            # File has content but wasn't built - might be an issue
                            status_info = {
                                "status": "not_implemented",
                                "errors": [],
                                "warnings": [],
                                "has_sorry": False,
                            }
                except IOError:
                    status_info = {
                        "status": "not_implemented",
                        "errors": [],
                        "warnings": [],
                        "has_sorry": False,
                    }

            # Add node association if available
            node_id = module_to_node.get(module_name)

            modules_dict = validation_results["modules"]
            assert isinstance(modules_dict, dict)  # Type narrowing for MyPy
            modules_dict[module_name] = {
                "status": status_info["status"],
                "errors": status_info["errors"],
                "warnings": status_info["warnings"],
                "has_sorry": status_info["has_sorry"],
                "node_id": node_id,
                "file_path": str(module_path.relative_to(PROJECT_ROOT)),
            }

            # Update summary
            validation_results["summary"]["total"] += 1
            validation_results["summary"][status_info["status"]] += 1

        # Save validation results
        with open(VALIDATION_RESULTS_PATH, "w", encoding="utf-8") as f:
            json.dump(validation_results, f, indent=2)

        # Print summary
        print("\n" + "=" * 60)
        print("Lean Proof Validation Summary:")
        print("=" * 60)
        print(f"Total modules: {validation_results['summary']['total']}")
        print(f"✅ Completed: {validation_results['summary']['completed']}")
        print(f"⚠️  Warnings present: {validation_results['summary']['warnings_present']}")
        print(f"❌ Errors present: {validation_results['summary']['errors_present']}")
        print(f"📝 Not implemented: {validation_results['summary']['not_implemented']}")
        print("=" * 60)

        # Print details for modules with issues
        if validation_results["summary"]["errors_present"] > 0:
            print("\n❌ Modules with errors:")
            for module_name, info in validation_results["modules"].items():
                if info["status"] == "errors_present":
                    print(f"  - {module_name}")
                    for error in info["errors"][:3]:  # Show first 3 errors
                        msg = f"{error['file']}:{error['line']}:{error['column']}: "
                        msg += f"{error['message']}"
                        print(f"    {msg}")
                    if len(info["errors"]) > 3:
                        print(f"    ... and {len(info['errors']) - 3} more errors")

        if validation_results["summary"]["warnings_present"] > 0:
            print("\n⚠️  Modules with warnings:")
            for module_name, info in validation_results["modules"].items():
                if info["status"] == "warnings_present":
                    print(f"  - {module_name}")
                    if info["has_sorry"]:
                        print("    Contains 'sorry' (incomplete proof)")
                    for warning in info["warnings"][:2]:  # Show first 2 warnings
                        msg = f"{warning['file']}:{warning['line']}:{warning['column']}: "
                        msg += f"{warning['message']}"
                        print(f"    {msg}")
                    if len(info["warnings"]) > 2:
                        print(f"    ... and {len(info['warnings']) - 2} more warnings")

        print(f"\nValidation results saved to: {VALIDATION_RESULTS_PATH}")

        # Return success if no errors (warnings are OK)
        errors_present = validation_results["summary"]["errors_present"]
        return bool(errors_present == 0)

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
