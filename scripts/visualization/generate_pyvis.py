#!/usr/bin/env python3
"""
Generate PyVis Interactive Visualizations for All Nodes

This script generates interactive HTML visualizations for all nodes
in the knowledge graph as part of the build pipeline.
"""

import sys
from pathlib import Path
import logging
from typing import List

# Add the project root to the Python path
project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root))

# pylint: disable=import-error,wrong-import-position
try:
    from viz.pyvis_graphs import (  # noqa: E402
        generate_all_node_graphs,
        create_domain_overview,
        save_as_html,
    )
except ImportError as e:
    print(f"Error importing viz.pyvis_graphs: {e}")
    print(f"Project root: {project_root}")
    print(f"sys.path: {sys.path}")
    sys.exit(1)
# pylint: enable=import-error,wrong-import-position

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


def main() -> None:
    """Generate all interactive visualizations."""
    ttl_path = project_root / "knowledge_graph.ttl"

    if not ttl_path.exists():
        logger.error("Knowledge graph not found at %s", ttl_path)
        logger.error("Please run build_graph.py first")
        sys.exit(1)

    logger.info("Starting PyVis visualization generation...")

    # Generate individual node graphs
    logger.info("Generating individual node visualizations...")
    generate_all_node_graphs(ttl_path)

    # Generate domain overview graphs
    logger.info("Generating domain overview visualizations...")
    domains = [
        "Algebra",
        "Topology",
        "Analysis",
        "Number Theory",
        "Logic and Set Theory",
        "Geometry",
        "Category Theory",
        "Combinatorics",
        "Probability and Statistics",
    ]

    for domain in domains:
        try:
            logger.info("Creating overview for %s...", domain)
            net = create_domain_overview(domain, ttl_path)
            save_as_html(net, f"domain-{domain.lower().replace(' ', '-')}")
        except (ValueError, IOError) as e:
            logger.warning("Could not create overview for %s: %s", domain, e)

    # Generate a summary
    output_dir = project_root / "output" / "interactive"
    html_files = list(output_dir.glob("*.html"))
    logger.info("Successfully generated %d interactive visualizations", len(html_files))

    # Create an index file listing all visualizations
    create_visualization_index(output_dir, html_files)

    logger.info("PyVis visualization generation complete!")


def create_visualization_index(output_dir: Path, html_files: List[Path]) -> None:
    """Create an index HTML file listing all available visualizations."""
    index_content = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Math Knowledge Graph - Interactive Visualizations</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto,
                "Helvetica Neue", Arial, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background-color: #f5f5f5;
        }
        h1 {
            color: #333;
            text-align: center;
            margin-bottom: 30px;
        }
        .section {
            background: white;
            border-radius: 8px;
            padding: 20px;
            margin-bottom: 20px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        h2 {
            color: #2196F3;
            margin-top: 0;
        }
        .viz-grid {
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(200px, 1fr));
            gap: 10px;
            margin-top: 15px;
        }
        .viz-link {
            display: block;
            padding: 10px;
            background: #f0f0f0;
            border-radius: 4px;
            text-decoration: none;
            color: #333;
            transition: background-color 0.3s;
        }
        .viz-link:hover {
            background: #e0e0e0;
        }
        .domain-link {
            background: #E3F2FD;
            font-weight: bold;
        }
        .domain-link:hover {
            background: #BBDEFB;
        }
    </style>
</head>
<body>
    <h1>Math Knowledge Graph - Interactive Visualizations</h1>

    <div class="section">
        <h2>Domain Overviews</h2>
        <div class="viz-grid">
"""

    # Add domain overview links
    domain_files = sorted([f for f in html_files if f.name.startswith("domain-")])
    for file in domain_files:
        domain_name = file.stem.replace("domain-", "").replace("-", " ").title()
        link = f'<a href="{file.name}" class="viz-link domain-link">{domain_name}</a>'
        index_content += f"            {link}\n"

    index_content += """        </div>
    </div>

    <div class="section">
        <h2>Individual Node Visualizations</h2>
        <div class="viz-grid">
"""

    # Add individual node links
    node_files = sorted([f for f in html_files if not f.name.startswith("domain-")])
    for file in node_files:
        index_content += f'            <a href="{file.name}" class="viz-link">{file.stem}</a>\n'

    index_content += (
        """        </div>
    </div>

    <div class="section">
        <p style="text-align: center; color: #666; margin: 0;">
            Generated by Math Knowledge Graph Build System<br>
            Total visualizations: """
        + str(len(html_files))
        + """
        </p>
    </div>
</body>
</html>"""
    )

    index_path = output_dir / "index.html"
    index_path.write_text(index_content)
    logger.info("Created visualization index at %s", index_path)


if __name__ == "__main__":
    main()
