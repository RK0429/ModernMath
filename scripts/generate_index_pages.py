#!/usr/bin/env python3
"""Generate comprehensive index.qmd files for each mathematical domain."""

from pathlib import Path
from typing import Dict, List, Tuple

import frontmatter


def categorize_files(files: List[str]) -> Dict[str, List[Tuple[str, str]]]:
    """Categorize .qmd files by their type prefix."""
    categories: Dict[str, List[Tuple[str, str]]] = {
        "definitions": [],
        "theorems": [],
        "examples": [],
        "axioms": [],
    }

    for file in files:
        file_path = Path(file)
        filename = file_path.name

        if filename == "index.qmd" or filename.startswith("_"):
            continue

        # Load the file to get its title
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                post = frontmatter.load(f)
                title = post.metadata.get("title", file_path.stem)
        except (IOError, OSError):
            title = file_path.stem.replace("-", " ").title()

        if filename.startswith("def-"):
            categories["definitions"].append((filename, title))
        elif filename.startswith("thm-"):
            categories["theorems"].append((filename, title))
        elif filename.startswith("ex-"):
            categories["examples"].append((filename, title))
        elif filename.startswith("ax-"):
            categories["axioms"].append((filename, title))

    # Sort each category by filename
    for items in categories.values():
        items.sort(key=lambda x: x[0])

    return categories


def generate_index_content(domain: str, domain_path: Path, lang: str = "en") -> str:
    """Generate the content for an index.qmd file."""
    # Get all .qmd files in the domain
    qmd_files = list(domain_path.glob("*.qmd"))
    qmd_file_names = [f.name for f in qmd_files if f.name != "index.qmd"]

    # Categorize files
    categories = categorize_files([str(domain_path / f) for f in qmd_file_names])

    # Domain descriptions in English
    descriptions_en = {
        "algebra": "Algebra is the study of mathematical symbols and the rules for "
        "manipulating these symbols. It is a unifying thread of almost all "
        "of mathematics.",
        "analysis": "Mathematical Analysis forms the foundation of calculus and advanced "
        "mathematics. It provides rigorous definitions and proofs for "
        "concepts that are often introduced intuitively in calculus courses.",
        "topology": "Topology is the mathematical study of shapes and spaces. It focuses "
        "on properties that are preserved under continuous deformations.",
        "geometry": "Geometry is the branch of mathematics concerned with questions of "
        "shape, size, relative position of figures, and the properties "
        "of space.",
        "number-theory": "Number Theory is the study of integers and integer-valued "
        "functions. It is one of the oldest and most fundamental "
        "branches of mathematics.",
        "combinatorics": "Combinatorics is the mathematics of counting, arranging, "
        "and analyzing discrete structures.",
        "logic-set-theory": "Logic and Set Theory form the foundation of modern "
        "mathematics, providing the language and basic concepts "
        "upon which all mathematical theories are built.",
        "probability-statistics": "Probability and Statistics provide the mathematical "
        "framework for understanding uncertainty and making "
        "inferences from data.",
        "category-theory": "Category Theory is a general mathematical theory of "
        "structures and systems of structures. It provides a "
        "unifying language for mathematics.",
    }

    # Domain descriptions in Japanese
    descriptions_ja = {
        "algebra": "代数学は数学記号とそれらの記号を操作する規則の研究です。"
        "これはほぼすべての数学を統一する糸です。",
        "analysis": "数学的解析は微積分学と高等数学の基礎を形成します。"
        "微積分コースで直感的に導入される概念に対して、厳密な定義と証明を提供します。",
        "topology": "位相空間論は形と空間の数学的研究です。連続変形の下で保存される性質に焦点を当てています。",
        "geometry": "幾何学は、図形の形状、大きさ、相対的位置、および空間の性質に関する数学の分野です。",
        "number-theory": "数論は整数と整数値関数の研究です。"
        "これは数学の最も古く、最も基本的な分野の1つです。",
        "combinatorics": "組合せ論は、離散構造の数え上げ、配列、分析の数学です。",
        "logic-set-theory": "論理学と集合論は現代数学の基礎を形成し、"
        "すべての数学理論が構築される言語と基本概念を提供します。",
        "probability-statistics": "確率統計は、不確実性を理解し、"
        "データから推論を行うための数学的枠組みを提供します。",
        "category-theory": "圏論は構造と構造のシステムの一般的な数学理論です。"
        "数学のための統一言語を提供します。",
    }

    # Choose descriptions based on language
    descriptions = descriptions_ja if lang == "ja" else descriptions_en

    # Domain names in Japanese
    domain_names_ja = {
        "algebra": "代数学",
        "analysis": "解析学",
        "topology": "位相空間論",
        "geometry": "幾何学",
        "number-theory": "数論",
        "combinatorics": "組合せ論",
        "logic-set-theory": "論理学・集合論",
        "probability-statistics": "確率統計",
        "category-theory": "圏論",
    }

    # Get the domain title based on language
    if lang == "ja":
        domain_title = domain_names_ja.get(domain, domain.replace("-", " ").title())
    else:
        domain_title = domain.replace("-", " ").title()

    # Start building the content
    content = f"""---
title: "{domain_title}"
---

# {domain_title}

{descriptions.get(domain,
                  f"Welcome to the {domain_title} section of the "
                  f"Mathematics Knowledge Graph Wiki.")}

## {'コンテンツ' if lang == 'ja' else 'Contents'}

"""

    # Section titles based on language
    section_titles = {
        "axioms": "公理" if lang == "ja" else "Axioms",
        "definitions": "定義" if lang == "ja" else "Definitions",
        "theorems": "定理" if lang == "ja" else "Theorems",
        "examples": "例" if lang == "ja" else "Examples",
    }

    # Add axioms if any
    if categories["axioms"]:
        content += f"### {section_titles['axioms']}\n\n"
        for file, title in categories["axioms"]:
            content += f"- [{title}]({Path(file).name})\n"
        content += "\n"

    # Add definitions
    if categories["definitions"]:
        content += f"### {section_titles['definitions']}\n\n"
        for file, title in categories["definitions"]:
            content += f"- [{title}]({Path(file).name})\n"
        content += "\n"

    # Add theorems
    if categories["theorems"]:
        content += f"### {section_titles['theorems']}\n\n"
        for file, title in categories["theorems"]:
            content += f"- [{title}]({Path(file).name})\n"
        content += "\n"

    # Add examples
    if categories["examples"]:
        content += f"### {section_titles['examples']}\n\n"
        for file, title in categories["examples"]:
            content += f"- [{title}]({Path(file).name})\n"
        content += "\n"

    # Add footer
    if lang == "ja":
        content += """## ナビゲーション

- サイドバーを使用して、このドメインのすべてのトピックを閲覧できます
- [可視化](../../visualizations-ja.html)ページで知識グラフを探索できます
- [検索](../../search-ja.html)機能を使用して特定の概念を見つけることができます

## 貢献

このWikiは積極的に開発されています。貢献や問題の報告については、
[GitHubリポジトリ](https://github.com/RK0429/ModernMath)をご覧ください。
"""
    else:
        content += """## Navigation

- Use the sidebar to browse all topics in this domain
- Visit the [Visualizations](../../visualizations.html) page to explore the knowledge graph
- Use the [Search](../../search.html) function to find specific concepts

## Contributing

This wiki is actively being developed. If you'd like to contribute or report issues,
please visit our [GitHub repository](https://github.com/RK0429/ModernMath).
"""

    return content


def main() -> None:
    """Generate index.qmd files for all domains."""
    content_dir = Path("content")

    if not content_dir.exists():
        print(f"Error: {content_dir} directory not found!")
        return

    # Check if we have multilingual structure (en/ja directories)
    lang_dirs = [d for d in content_dir.iterdir() if d.is_dir() and d.name in ["en", "ja"]]

    if lang_dirs:
        # Process multilingual structure
        for lang_dir in lang_dirs:
            print(f"\nProcessing {lang_dir.name} language content...")
            domains = [d for d in lang_dir.iterdir() if d.is_dir() and not d.name.startswith("_")]

            for domain_path in domains:
                domain = domain_path.name
                print(f"  Generating index for {lang_dir.name}/{domain}...")

                # Generate the index content with language parameter
                content = generate_index_content(domain, domain_path, lang_dir.name)

                # Write to index.qmd
                index_path = domain_path / "index.qmd"
                with open(index_path, "w", encoding="utf-8") as f:
                    f.write(content)

                print(f"    Created {index_path}")
    else:
        # Process flat structure (backward compatibility)
        domains = [d for d in content_dir.iterdir() if d.is_dir() and not d.name.startswith("_")]

        for domain_path in domains:
            domain = domain_path.name
            print(f"Generating index for {domain}...")

            # Generate the index content
            content = generate_index_content(domain, domain_path)

            # Write to index.qmd
            index_path = domain_path / "index.qmd"
            with open(index_path, "w", encoding="utf-8") as f:
                f.write(content)

            print(f"  Created {index_path}")

    print("\nAll index files generated successfully!")


if __name__ == "__main__":
    main()
