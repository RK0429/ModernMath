#!/usr/bin/env python3
"""
Build a full-text search index from all content files.
"""

import logging
import re
from pathlib import Path
from typing import Dict, List

import frontmatter
from whoosh import index
from whoosh.fields import ID, TEXT, KEYWORD, Schema
from whoosh.qparser import MultifieldParser, FuzzyTermPlugin
from whoosh.analysis import StemmingAnalyzer

logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


# Define the search schema
def create_schema() -> Schema:
    """Create the schema for the search index"""
    return Schema(
        # Unique identifier (same as RDF node ID)
        id=ID(stored=True, unique=True),
        # File path for reference
        path=ID(stored=True),
        # Title from YAML front matter
        title=TEXT(stored=True, analyzer=StemmingAnalyzer()),
        # Type (Definition, Theorem, etc.)
        type=KEYWORD(stored=True),
        # Domain (Algebra, Topology, etc.)
        domain=KEYWORD(stored=True),
        # Status (complete, draft, etc.)
        status=KEYWORD(stored=True),
        # Full content of the file (searchable but not stored to save space)
        content=TEXT(analyzer=StemmingAnalyzer()),
        # List of dependencies/requirements
        requires=TEXT(stored=True),
        # Extracted keywords and important terms
        keywords=TEXT(stored=True, analyzer=StemmingAnalyzer()),
        # Brief description/summary (first paragraph)
        description=TEXT(stored=True),
    )


def extract_keywords(content: str) -> List[str]:
    """Extract important mathematical terms from content"""
    keywords = set()

    # Extract terms in bold
    bold_terms = re.findall(r"\*\*(.*?)\*\*", content)
    keywords.update(bold_terms)

    # Extract terms in italics
    italic_terms = re.findall(r"\*(.*?)\*", content)
    keywords.update(italic_terms)

    # Extract mathematical terms in $...$
    math_terms = re.findall(r"\$([^$]+)\$", content)
    # Filter out complex expressions, keep simple terms
    for term in math_terms:
        if len(term) < 30 and not any(op in term for op in ["=", "+", "-", "/", "^"]):
            keywords.add(term)

    # Remove very short keywords
    keywords = {k for k in keywords if len(k) > 2}

    return list(keywords)


def extract_description(content: str) -> str:
    """Extract a brief description from the content (first meaningful paragraph)"""
    # Remove YAML front matter if present
    content = re.sub(r"^---\n.*?\n---\n", "", content, flags=re.DOTALL)

    # Remove headers
    content = re.sub(r"^#+\s+.*$", "", content, flags=re.MULTILINE)

    # Remove code blocks
    content = re.sub(r"```.*?```", "", content, flags=re.DOTALL)

    # Remove mermaid diagrams
    content = re.sub(r"```\{mermaid\}.*?```", "", content, flags=re.DOTALL)

    # Find first non-empty paragraph
    paragraphs = content.strip().split("\n\n")
    for para in paragraphs:
        para = para.strip()
        if para and len(para) > 20 and not para.startswith((":::",)):
            # Clean up the paragraph
            para = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", para)  # Remove links
            para = re.sub(r"[#*_`]", "", para)  # Remove markdown formatting
            return para[:300] + "..." if len(para) > 300 else para

    return ""


def get_domain_from_path(file_path: Path) -> str:
    """Extract domain from file path"""
    # Map directory names to readable domain names
    domain_map = {
        "algebra": "Algebra",
        "topology": "Topology",
        "analysis": "Analysis",
        "number-theory": "Number Theory",
        "logic-set-theory": "Logic & Set Theory",
        "geometry": "Geometry",
        "category-theory": "Category Theory",
        "combinatorics": "Combinatorics",
        "probability-statistics": "Probability & Statistics",
    }

    # Get the parent directory name
    parent = file_path.parent.name
    return domain_map.get(parent, parent.title())


def index_content_files(content_dir: Path, index_dir: Path):
    """Build the search index from all content files"""
    # Create or open the index
    if not index_dir.exists():
        index_dir.mkdir(parents=True)
        ix = index.create_in(str(index_dir), create_schema())
        logger.info(f"Created new index in {index_dir}")
    else:
        ix = index.open_dir(str(index_dir))
        logger.info(f"Opened existing index in {index_dir}")

    writer = ix.writer()
    indexed_count = 0

    # Process all .qmd files
    for qmd_file in content_dir.rglob("*.qmd"):
        # Skip index files
        if qmd_file.name == "index.qmd":
            continue

        try:
            with open(qmd_file, "r", encoding="utf-8") as f:
                post = frontmatter.load(f)
                metadata = post.metadata
                content = post.content

            # Extract required fields
            doc_id = metadata.get("id", qmd_file.stem)
            title = metadata.get("title", "")
            doc_type = metadata.get("type", "Unknown")
            status = metadata.get("status", "draft")
            requires = metadata.get("requires", [])

            # Get domain from path
            domain = get_domain_from_path(qmd_file)

            # Extract keywords and description
            keywords = extract_keywords(content)
            description = extract_description(content)

            # Add document to index
            writer.add_document(
                id=doc_id,
                path=str(qmd_file.relative_to(content_dir)),
                title=title,
                type=doc_type,
                domain=domain,
                status=status,
                content=content,
                requires=" ".join(requires) if requires else "",
                keywords=" ".join(keywords),
                description=description,
            )

            indexed_count += 1
            logger.info(f"Indexed: {doc_id} ({title})")

        except Exception as e:
            logger.error(f"Error indexing {qmd_file}: {e}")

    writer.commit()
    logger.info(f"Successfully indexed {indexed_count} documents")


def search_index(query_str: str, index_dir: Path, limit: int = 50) -> List[Dict]:
    """Search the index for a query string"""
    if not index_dir.exists():
        logger.error(f"Index directory {index_dir} does not exist")
        return []

    ix = index.open_dir(str(index_dir))

    # Create a multi-field parser that searches across title, content, and keywords
    parser = MultifieldParser(
        ["title", "content", "keywords", "description"], ix.schema
    )
    # Add fuzzy matching support
    parser.add_plugin(FuzzyTermPlugin())

    query = parser.parse(query_str)

    results = []
    with ix.searcher() as searcher:
        hits = searcher.search(query, limit=limit)

        for hit in hits:
            results.append(
                {
                    "id": hit["id"],
                    "title": hit["title"],
                    "type": hit["type"],
                    "domain": hit["domain"],
                    "path": hit["path"],
                    "description": hit.get("description", ""),
                    "score": hit.score,
                }
            )

    return results


def main():
    """Main function to build the search index"""
    # Get project root
    project_root = Path(__file__).parent.parent
    content_dir = project_root / "content"
    index_dir = project_root / "search_index"

    if not content_dir.exists():
        logger.error(f"Content directory {content_dir} does not exist")
        return

    logger.info("Building search index...")
    index_content_files(content_dir, index_dir)

    # Test the search
    logger.info("\nTesting search functionality...")
    test_queries = ["group", "topology", "continuous", "theorem"]

    for query in test_queries:
        logger.info(f"\nSearching for: '{query}'")
        results = search_index(query, index_dir, limit=5)
        for i, result in enumerate(results, 1):
            logger.info(f"  {i}. {result['title']} (Score: {result['score']:.2f})")


if __name__ == "__main__":
    main()
