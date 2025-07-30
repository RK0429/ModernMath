#!/usr/bin/env python3
"""
Embed Lean 4 Proofs in Articles

This script processes Quarto files and adds Lean 4 proof sections with embedded
iframes that load the proofs in the Lean web editor.
"""

import json
import logging
import os
import re
import subprocess
from pathlib import Path
from typing import Dict, Optional

import frontmatter

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


class LeanProofEmbedder:
    """Embed Lean 4 proofs in Quarto articles."""

    # pylint: disable=too-few-public-methods

    def __init__(self, content_dir: Path, lean_mappings_path: Path, github_base_url: str):
        """
        Initialize the embedder.

        Args:
            content_dir: Path to content directory
            lean_mappings_path: Path to lean_mappings.json
            github_base_url: Base URL for GitHub Pages (e.g., https://username.github.io/repo)
        """
        self.content_dir = content_dir
        self.lean_mappings_path = lean_mappings_path
        self.github_base_url = github_base_url.rstrip("/")
        self.lean_mappings = self._load_lean_mappings()

    def _load_lean_mappings(self) -> Dict[str, Dict[str, Dict[str, str]]]:
        """Load Lean mappings from JSON file."""
        if not self.lean_mappings_path.exists():
            logger.warning("Lean mappings file not found: %s", self.lean_mappings_path)
            return {}

        try:
            with open(self.lean_mappings_path, "r", encoding="utf-8") as f:
                data: Dict[str, Dict[str, Dict[str, str]]] = json.load(f)
                return data
        except (IOError, json.JSONDecodeError) as e:
            logger.error("Error loading Lean mappings: %s", e)
            return {}

    def _get_lean_file_path(self, module_name: str) -> Optional[str]:
        """
        Get the path to the Lean file for a given module.

        Args:
            module_name: The module name (e.g., MathKnowledgeGraph.Algebra.Groups)

        Returns:
            Relative path to the Lean file, or None if not found
        """
        # Map module name to file path
        # e.g., MathKnowledgeGraph.Algebra.Groups -> formal/MathKnowledgeGraph/Algebra/Groups.lean
        if module_name.startswith("MathKnowledgeGraph"):
            parts = module_name.split(".")
            file_path = Path("formal") / Path(*parts)
            return f"{file_path}.lean"
        return None

    def _create_formal_proof_section(
        self, node_id: str, lean_data: Dict[str, str], language: str = "en"
    ) -> str:
        """
        Create the formal proof section HTML.

        Args:
            node_id: The node ID (e.g., def-group)
            lean_data: The Lean data from mappings
            language: Language code ('en' or 'ja')

        Returns:
            HTML string for the formal proof section
        """
        lean_id = lean_data.get("lean_id", "")
        module_name = lean_data.get("module_name", "")

        # Get the Lean file path
        lean_file_path = self._get_lean_file_path(module_name)
        if not lean_file_path:
            logger.warning("Could not determine Lean file path for %s", node_id)
            return ""

        # Construct the full URL to the Lean file on GitHub Pages
        lean_file_url = f"{self.github_base_url}/{lean_file_path}"

        # Construct the Lean web editor URL
        lean_editor_url = f"https://live.lean-lang.org/#url={lean_file_url}"

        # Create the section content
        if language == "ja":
            title = "形式的証明"
            description = (
                "この定義は Lean 4 で形式的に検証されています。"
                "下のインタラクティブエディタで証明を探索できます："
            )
            fallback_text = "ブラウザが iframe をサポートしていません。"
            view_fullscreen = "フルスクリーンで表示"
        else:
            title = "Formal Proof"
            description = (
                "This definition has been formally verified in Lean 4. "
                "You can explore the proof in the interactive editor below:"
            )
            fallback_text = "Your browser does not support iframes."
            view_fullscreen = "View in fullscreen"

        # Note: Using triple backticks to properly escape the HTML block
        section_html = f"""

## {title}

{description}

```{{=html}}
<div class="lean-proof-container" style="margin: 1em 0;">
  <iframe
    src="{lean_editor_url}"
    width="100%"
    height="600"
    style="border: 1px solid #ddd; border-radius: 4px; box-shadow: 0 2px 4px rgba(0,0,0,0.1);"
    title="Lean 4 Interactive Proof">
    <p>{fallback_text}</p>
  </iframe>
  <p style="text-align: right; margin-top: 0.5em;">
    <a href="{lean_editor_url}" target="_blank" rel="noopener noreferrer">
      {view_fullscreen} →
    </a>
  </p>
</div>
```

**Lean ID**: `{lean_id}`
**Module**: `{module_name}`
"""
        return section_html

    def embed_proofs(self) -> None:
        """Process all Quarto files and embed Lean proofs where applicable."""
        if not self.lean_mappings:
            logger.warning("No Lean mappings available, skipping proof embedding")
            return

        node_to_lean = self.lean_mappings.get("node_to_lean", {})
        if not node_to_lean:
            logger.warning("No node-to-Lean mappings found")
            return

        # Process all .qmd files
        qmd_files = list(self.content_dir.rglob("*.qmd"))
        embedded_count = 0

        for qmd_path in qmd_files:
            try:
                # Load the file
                with open(qmd_path, "r", encoding="utf-8") as f:
                    post = frontmatter.load(f)

                metadata = post.metadata
                content = post.content

                # Skip if no ID or if ID not in Lean mappings
                if "id" not in metadata:
                    continue

                node_id = metadata["id"]
                if node_id not in node_to_lean:
                    continue

                # Check if proof section already exists
                if "## Formal Proof" in content or "## 形式的証明" in content:
                    logger.info("Proof section already exists in %s", qmd_path)
                    continue

                # Detect language from path
                language = self._get_language_from_path(qmd_path)

                # Get Lean data
                lean_data = node_to_lean[node_id]

                # Create the formal proof section
                proof_section = self._create_formal_proof_section(node_id, lean_data, language)

                # Find where to insert the proof section
                # Insert before "## Dependency Graph" if it exists, otherwise at the end
                dep_graph_match = re.search(r"\n## Dependency Graph", content)
                if dep_graph_match:
                    insert_pos = dep_graph_match.start()
                    new_content = content[:insert_pos] + proof_section + content[insert_pos:]
                else:
                    # Insert at the end
                    new_content = content.rstrip() + "\n" + proof_section

                # Write the updated content
                with open(qmd_path, "w", encoding="utf-8") as f:
                    # Update the content in the post object
                    post.content = new_content
                    # Use frontmatter.dumps to write the entire post
                    f.write(frontmatter.dumps(post))

                logger.info("Embedded Lean proof in %s", qmd_path)
                embedded_count += 1

            except (IOError, json.JSONDecodeError, ValueError) as e:
                logger.error("Error processing %s: %s", qmd_path, e)

        logger.info("Embedded Lean proofs in %d files", embedded_count)

    def _get_language_from_path(self, qmd_path: Path) -> str:
        """Detect language from file path."""
        relative_path = qmd_path.relative_to(self.content_dir)
        if len(relative_path.parts) > 0 and relative_path.parts[0] in ["en", "ja"]:
            return str(relative_path.parts[0])
        return "en"


def main() -> None:
    """Main entry point."""
    # Set up paths
    project_root = Path(__file__).parent.parent.parent
    content_dir = project_root / "content"
    lean_mappings_path = project_root / "lean_mappings.json"

    # GitHub Pages URL - detect from git remote or use environment variable
    github_base_url = os.environ.get("GITHUB_PAGES_URL")

    if not github_base_url:
        try:
            # Try to detect from git remote
            result = subprocess.run(
                ["git", "remote", "get-url", "origin"], capture_output=True, text=True, check=True
            )
            remote_url = result.stdout.strip()

            # Extract username and repo from remote URL
            # Handle both SSH and HTTPS formats
            if remote_url.startswith("git@github.com:"):
                # SSH format: git@github.com:username/repo.git
                parts = remote_url.replace("git@github.com:", "").replace(".git", "").split("/")
            elif remote_url.startswith("https://github.com/"):
                # HTTPS format: https://github.com/username/repo.git
                parts = remote_url.replace("https://github.com/", "").replace(".git", "").split("/")
            else:
                raise ValueError("Unknown remote URL format")

            if len(parts) >= 2:
                username, repo = parts[0], parts[1]
                # GitHub Pages URLs always use lowercase usernames
                github_base_url = f"https://{username.lower()}.github.io/{repo}"
            else:
                raise ValueError("Could not parse remote URL")

        except (subprocess.CalledProcessError, ValueError) as e:
            logger.warning("Could not detect GitHub Pages URL: %s", e)
            # Default fallback
            github_base_url = "https://rk0429.github.io/ModernMath"
            logger.info("Using default GitHub Pages URL: %s", github_base_url)

    logger.info("Using GitHub Pages URL: %s", github_base_url)

    # Create embedder and process files
    embedder = LeanProofEmbedder(content_dir, lean_mappings_path, github_base_url)
    embedder.embed_proofs()


if __name__ == "__main__":
    main()
