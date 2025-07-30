#!/usr/bin/env python3
"""
Generate Formal Proof Progress Page

This script generates a page showing the progress of formal proofs across
all mathematical concepts in the knowledge graph.
"""

import json
import logging
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Any

import frontmatter

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


class ProofProgressGenerator:
    """Generate formal proof progress pages."""

    def __init__(self, content_dir: Path, lean_mappings_path: Path, output_dir: Path):
        """
        Initialize the generator.

        Args:
            content_dir: Path to content directory
            lean_mappings_path: Path to lean_mappings.json
            output_dir: Path to output directory for generated pages
        """
        self.content_dir = content_dir
        self.lean_mappings_path = lean_mappings_path
        self.output_dir = output_dir
        self.lean_mappings = self._load_lean_mappings()

    def _load_lean_mappings(self) -> Dict[str, Dict[str, Any]]:
        """Load Lean mappings from JSON file."""
        empty_mappings: Dict[str, Dict[str, Any]] = {}
        if not self.lean_mappings_path.exists():
            logger.warning("Lean mappings file not found: %s", self.lean_mappings_path)
            return empty_mappings

        try:
            with open(self.lean_mappings_path, "r", encoding="utf-8") as f:
                loaded_data = json.load(f)
                return loaded_data if isinstance(loaded_data, dict) else empty_mappings
        except (IOError, json.JSONDecodeError) as e:
            logger.error("Error loading Lean mappings: %s", e)
            return empty_mappings

    def _collect_proof_data(self) -> Dict[str, List[Dict[str, Any]]]:
        """Collect data about formal proofs organized by domain."""
        proof_data: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        node_to_lean = self.lean_mappings.get("node_to_lean", {})

        # Process all .qmd files to get complete article list
        qmd_files = list(self.content_dir.glob("en/*/*.qmd"))

        for qmd_path in qmd_files:
            # Skip index files
            if qmd_path.name == "index.qmd":
                continue

            try:
                with open(qmd_path, "r", encoding="utf-8") as f:
                    post = frontmatter.load(f)

                metadata = post.metadata
                if "id" not in metadata or "type" not in metadata:
                    continue

                node_id = metadata["id"]
                node_type = metadata["type"]
                title = metadata.get("title", node_id)
                status = metadata.get("status", "draft")

                # Get domain from path
                domain = qmd_path.parent.name

                # Check if this node has a formal proof
                has_proof = node_id in node_to_lean
                lean_data = node_to_lean.get(node_id, {})

                article_info = {
                    "id": node_id,
                    "title": title,
                    "type": node_type,
                    "status": status,
                    "has_proof": has_proof,
                    "lean_id": lean_data.get("lean_id", ""),
                    "module_name": lean_data.get("module_name", ""),
                    "path": f"../en/{domain}/{qmd_path.name}",
                }

                proof_data[domain].append(article_info)

            except (OSError, ValueError, KeyError) as e:
                logger.error("Error processing %s: %s", qmd_path, e)

        # Sort articles within each domain by type and then by title
        type_order = [
            "Axiom",
            "Definition",
            "Theorem",
            "Proposition",
            "Lemma",
            "Corollary",
            "Example",
        ]
        for domain in proof_data:
            proof_data[domain].sort(
                key=lambda x: (
                    type_order.index(x["type"]) if x["type"] in type_order else 999,
                    x["title"].lower(),
                )
            )

        return dict(proof_data)

    def _calculate_statistics(self, proof_data: Dict[str, List[Dict[str, Any]]]) -> Dict[str, Any]:
        """Calculate statistics about formal proof coverage."""
        stats: Dict[str, Any] = {
            "total_articles": 0,
            "verified_articles": 0,
            "coverage_percentage": 0.0,
            "by_type": {},
            "by_domain": {},
        }

        for domain, articles in proof_data.items():
            for article in articles:
                stats["total_articles"] += 1

                # Initialize type stats if not exists
                if article["type"] not in stats["by_type"]:
                    stats["by_type"][article["type"]] = {"total": 0, "verified": 0}
                stats["by_type"][article["type"]]["total"] += 1

                # Initialize domain stats if not exists
                if domain not in stats["by_domain"]:
                    stats["by_domain"][domain] = {"total": 0, "verified": 0}
                stats["by_domain"][domain]["total"] += 1

                if article["has_proof"]:
                    stats["verified_articles"] += 1
                    stats["by_type"][article["type"]]["verified"] += 1
                    stats["by_domain"][domain]["verified"] += 1

        if stats["total_articles"] > 0:
            stats["coverage_percentage"] = (
                stats["verified_articles"] / stats["total_articles"] * 100
            )

        return stats

    def _generate_progress_bar(self, verified: int, total: int) -> str:
        """Generate a text-based progress bar."""
        if total == 0:
            return "N/A"

        percentage = verified / total * 100
        filled = int(percentage / 10)
        empty = 10 - filled

        progress_bar = "▓" * filled + "░" * empty
        return f"{progress_bar} {percentage:.1f}% ({verified}/{total})"

    def generate_progress_page(self, language: str = "en") -> None:
        """Generate the formal proof progress page."""
        # Collect proof data
        proof_data = self._collect_proof_data()
        stats = self._calculate_statistics(proof_data)

        # Create output directory and file in language-specific subdirectory
        output_path = self.output_dir / language / "proof-progress.qmd"
        output_path.parent.mkdir(parents=True, exist_ok=True)

        # Generate content
        if language == "ja":
            content = self._generate_japanese_content(proof_data, stats)
        else:
            content = self._generate_english_content(proof_data, stats)

        # Write the file
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(content)

        logger.info("Generated proof progress page: %s", output_path)

    def get_proof_statistics(self) -> Dict[str, Any]:
        """Get proof statistics without generating pages.

        Returns:
            Dictionary containing proof coverage statistics
        """
        proof_data = self._collect_proof_data()
        return self._calculate_statistics(proof_data)

    def _generate_english_content(
        self, proof_data: Dict[str, List[Dict[str, Any]]], stats: Dict[str, Any]
    ) -> str:
        """Generate English version of the progress page."""
        content = """---
title: "Formal Proof Progress"
description: "Track the progress of formal verification in Lean 4"
---

# Formal Proof Progress

This page tracks the progress of formal verification for mathematical concepts in our knowledge
graph using Lean 4.

## Overall Progress

"""

        # Overall statistics
        verified = stats["verified_articles"]
        total = stats["total_articles"]
        content += f"**Total Coverage**: {self._generate_progress_bar(verified, total)}\n\n"

        # Progress by type
        content += "### Progress by Type\n\n"
        for node_type, type_stats in sorted(stats["by_type"].items()):
            verified = type_stats["verified"]
            total = type_stats["total"]
            content += f"- **{node_type}**: "
            content += f"{self._generate_progress_bar(verified, total)}\n"

        content += "\n### Progress by Domain\n\n"
        for domain, domain_stats in sorted(stats["by_domain"].items()):
            domain_title = domain.replace("-", " ").title()
            verified = domain_stats["verified"]
            total = domain_stats["total"]
            content += f"- **{domain_title}**: "
            content += f"{self._generate_progress_bar(verified, total)}\n"

        # Detailed listing by domain
        content += "\n## Detailed Progress\n\n"

        for domain, articles in sorted(proof_data.items()):
            domain_title = domain.replace("-", " ").title()
            content += f"### {domain_title}\n\n"

            # Create a table
            content += "| Concept | Type | Status | Formal Proof |\n"
            content += "|---------|------|--------|-------------|\n"

            for article in articles:
                title_link = f"[{article['title']}]({article['path']})"
                type_badge = self._get_type_badge(article["type"])
                status_badge = self._get_status_badge(article["status"])
                if article["has_proof"]:
                    proof_status = "✅ Verified"
                else:
                    proof_status = "❌ Not verified"

                content += f"| {title_link} | {type_badge} | "
                content += f"{status_badge} | {proof_status} |\n"

            content += "\n"

        # Add legend
        content += """## Legend

### Type Badges
- <span style="background-color:#e1f5fe;padding:2px 6px;border-radius:3px;">Definition</span>
- <span style="background-color:#f3e5f5;padding:2px 6px;border-radius:3px;">Theorem</span>
- <span style="background-color:#fff3e0;padding:2px 6px;border-radius:3px;">Axiom</span>
- <span style="background-color:#e8f5e9;padding:2px 6px;border-radius:3px;">Example</span>
- <span style="background-color:#fce4ec;padding:2px 6px;border-radius:3px;">Proposition</span>
- <span style="background-color:#f3e5f5;padding:2px 6px;border-radius:3px;">Lemma</span>
- <span style="background-color:#e0f2f1;padding:2px 6px;border-radius:3px;">Corollary</span>

### Status Badges
- <span style="background-color:#c8e6c9;padding:2px 6px;border-radius:3px;">complete</span>: \
Article is complete
- <span style="background-color:#fff9c4;padding:2px 6px;border-radius:3px;">draft</span>: \
Article is in draft state
- <span style="background-color:#b2dfdb;padding:2px 6px;border-radius:3px;">verified</span>: \
Article has been verified
- <span style="background-color:#ffccbc;padding:2px 6px;border-radius:3px;">stub</span>: \
Article is a stub

### Proof Status
- ✅ **Verified**: Formal proof exists in Lean 4
- ❌ **Not verified**: No formal proof yet
"""

        return content

    def _generate_japanese_content(
        self, proof_data: Dict[str, List[Dict[str, Any]]], stats: Dict[str, Any]
    ) -> str:
        """Generate Japanese version of the progress page."""
        # Split the method to reduce local variables
        content = self._generate_japanese_header()
        content += self._generate_japanese_statistics(stats)
        content += self._generate_japanese_details(proof_data)
        content += self._generate_japanese_legend()
        return content

    def _generate_japanese_header(self) -> str:
        """Generate Japanese header content."""
        return """---
title: "形式的証明の進捗"
description: "Lean 4による形式的検証の進捗状況"
---

# 形式的証明の進捗

このページでは、知識グラフ内の数学概念に対するLean 4を使用した形式的検証の進捗を追跡しています。

## 全体の進捗

"""

    def _generate_japanese_statistics(self, stats: Dict[str, Any]) -> str:
        """Generate Japanese statistics section."""
        content = ""

        # Overall statistics
        verified = stats["verified_articles"]
        total = stats["total_articles"]
        content += f"**全体のカバレッジ**: {self._generate_progress_bar(verified, total)}\n\n"

        # Progress by type
        content += "### タイプ別の進捗\n\n"
        type_translations = {
            "Definition": "定義",
            "Theorem": "定理",
            "Axiom": "公理",
            "Example": "例",
            "Proposition": "命題",
            "Lemma": "補題",
            "Corollary": "系",
        }
        for node_type, type_stats in sorted(stats["by_type"].items()):
            type_ja = type_translations.get(node_type, node_type)
            verified = type_stats["verified"]
            total = type_stats["total"]
            content += f"- **{type_ja}**: "
            content += f"{self._generate_progress_bar(verified, total)}\n"

        content += "\n### ドメイン別の進捗\n\n"
        domain_translations = {
            "algebra": "代数",
            "analysis": "解析",
            "category-theory": "圏論",
            "combinatorics": "組合せ論",
            "geometry": "幾何学",
            "logic-set-theory": "論理と集合論",
            "number-theory": "数論",
            "probability-statistics": "確率と統計",
            "topology": "位相幾何学",
        }
        for domain, domain_stats in sorted(stats["by_domain"].items()):
            domain_ja = domain_translations.get(domain, domain.replace("-", " ").title())
            verified = domain_stats["verified"]
            total = domain_stats["total"]
            content += f"- **{domain_ja}**: "
            content += f"{self._generate_progress_bar(verified, total)}\n"

        return content

    def _generate_japanese_details(self, proof_data: Dict[str, List[Dict[str, Any]]]) -> str:
        """Generate Japanese detailed progress section."""
        content = "\n## 詳細な進捗\n\n"

        domain_translations = {
            "algebra": "代数",
            "analysis": "解析",
            "category-theory": "圏論",
            "combinatorics": "組合せ論",
            "geometry": "幾何学",
            "logic-set-theory": "論理と集合論",
            "number-theory": "数論",
            "probability-statistics": "確率と統計",
            "topology": "位相幾何学",
        }

        for domain, articles in sorted(proof_data.items()):
            domain_ja = domain_translations.get(domain, domain.replace("-", " ").title())
            content += f"### {domain_ja}\n\n"

            # Create a table
            content += "| 概念 | タイプ | ステータス | 形式的証明 |\n"
            content += "|------|--------|------------|------------|\n"

            for article in articles:
                # Convert path to Japanese version
                ja_path = article["path"].replace("/en/", "/ja/")
                title_link = f"[{article['title']}]({ja_path})"
                type_badge = self._get_type_badge(article["type"], "ja")
                status_badge = self._get_status_badge(article["status"], "ja")
                if article["has_proof"]:
                    proof_status = "✅ 検証済み"
                else:
                    proof_status = "❌ 未検証"

                content += f"| {title_link} | {type_badge} | "
                content += f"{status_badge} | {proof_status} |\n"

            content += "\n"

        return content

    def _generate_japanese_legend(self) -> str:
        """Generate Japanese legend section."""
        return """## 凡例

### タイプバッジ
- <span style="background-color:#e1f5fe;padding:2px 6px;border-radius:3px;">定義</span>
- <span style="background-color:#f3e5f5;padding:2px 6px;border-radius:3px;">定理</span>
- <span style="background-color:#fff3e0;padding:2px 6px;border-radius:3px;">公理</span>
- <span style="background-color:#e8f5e9;padding:2px 6px;border-radius:3px;">例</span>
- <span style="background-color:#fce4ec;padding:2px 6px;border-radius:3px;">命題</span>
- <span style="background-color:#f3e5f5;padding:2px 6px;border-radius:3px;">補題</span>
- <span style="background-color:#e0f2f1;padding:2px 6px;border-radius:3px;">系</span>

### ステータスバッジ
- <span style="background-color:#c8e6c9;padding:2px 6px;border-radius:3px;">完成</span>: \
記事は完成しています
- <span style="background-color:#fff9c4;padding:2px 6px;border-radius:3px;">草稿</span>: \
記事は草稿状態です
- <span style="background-color:#b2dfdb;padding:2px 6px;border-radius:3px;">検証済み</span>: \
記事は検証されています
- <span style="background-color:#ffccbc;padding:2px 6px;border-radius:3px;">スタブ</span>: \
記事はスタブです

### 証明ステータス
- ✅ **検証済み**: Lean 4で形式的証明が存在します
- ❌ **未検証**: まだ形式的証明がありません
"""

    def _get_type_badge(self, node_type: str, language: str = "en") -> str:
        """Get HTML badge for node type."""
        colors = {
            "Definition": "#e1f5fe",
            "Theorem": "#f3e5f5",
            "Axiom": "#fff3e0",
            "Example": "#e8f5e9",
            "Proposition": "#fce4ec",
            "Lemma": "#f3e5f5",
            "Corollary": "#e0f2f1",
        }

        if language == "ja":
            type_names = {
                "Definition": "定義",
                "Theorem": "定理",
                "Axiom": "公理",
                "Example": "例",
                "Proposition": "命題",
                "Lemma": "補題",
                "Corollary": "系",
            }
            display_name = type_names.get(node_type, node_type)
        else:
            display_name = node_type

        color = colors.get(node_type, "#f5f5f5")
        style = f"background-color:{color};padding:2px 6px;border-radius:3px;"
        return f'<span style="{style}">{display_name}</span>'

    def _get_status_badge(self, status: str, language: str = "en") -> str:
        """Get HTML badge for status."""
        colors = {
            "complete": "#c8e6c9",
            "draft": "#fff9c4",
            "verified": "#b2dfdb",
            "stub": "#ffccbc",
        }

        if language == "ja":
            status_names = {
                "complete": "完成",
                "draft": "草稿",
                "verified": "検証済み",
                "stub": "スタブ",
            }
            display_name = status_names.get(status, status)
        else:
            display_name = status

        color = colors.get(status, "#f5f5f5")
        style = f"background-color:{color};padding:2px 6px;border-radius:3px;"
        return f'<span style="{style}">{display_name}</span>'


def main() -> None:
    """Main entry point."""
    # Set up paths
    project_root = Path(__file__).parent.parent.parent
    content_dir = project_root / "content"
    lean_mappings_path = project_root / "lean_mappings.json"
    output_dir = project_root / "nav"

    # Create generator
    generator = ProofProgressGenerator(content_dir, lean_mappings_path, output_dir)

    # Generate both English and Japanese versions
    generator.generate_progress_page("en")
    generator.generate_progress_page("ja")


if __name__ == "__main__":
    main()
