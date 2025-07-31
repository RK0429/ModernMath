#!/usr/bin/env python3
"""
Generate Mermaid diagrams for each node in the knowledge graph showing its local neighborhood.
"""

import json
from pathlib import Path
from typing import Dict, Set, Tuple, Any, Optional
import frontmatter
from rdflib import Graph, Namespace, RDF, RDFS, Literal


# Define namespaces
MYMATH = Namespace("https://mathwiki.org/ontology#")
BASE_URI = "https://mathwiki.org/resource/"
BASE = Namespace(BASE_URI)


def load_lean_data() -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """Load Lean mappings and validation results."""
    lean_mappings: Dict[str, Any] = {}
    lean_validation: Dict[str, Any] = {}

    # Load Lean mappings
    mappings_file = Path("lean_mappings.json")
    if mappings_file.exists():
        try:
            with open(mappings_file, "r", encoding="utf-8") as f:
                mappings_data = json.load(f)
                lean_mappings = mappings_data.get("node_to_lean", {})
        except (IOError, json.JSONDecodeError) as e:
            print(f"Warning: Could not load lean_mappings.json: {e}")

    # Load Lean validation results
    validation_file = Path("lean_validation_results.json")
    if validation_file.exists():
        try:
            with open(validation_file, "r", encoding="utf-8") as f:
                validation_data = json.load(f)
                # Index by node_id for quick lookup
                for module_data in validation_data.get("modules", {}).values():
                    if module_data.get("node_id"):
                        lean_validation[module_data["node_id"]] = module_data["status"]
        except (IOError, json.JSONDecodeError) as e:
            print(f"Warning: Could not load lean_validation_results.json: {e}")

    return lean_mappings, lean_validation


def load_knowledge_graph(ttl_file: Path) -> Graph:
    """Load the knowledge graph from TTL file."""
    g = Graph()
    g.parse(ttl_file, format="turtle")
    return g


def get_node_info(g: Graph, node_uri: Any, lang: str = "en") -> Dict[str, Any]:
    """Get information about a node with language preference."""
    info = {"id": str(node_uri).replace(BASE_URI, ""), "label": None, "type": None}

    # Get label with language preference
    labels = {}
    for label in g.objects(node_uri, RDFS.label):
        # Extract language from literal
        if isinstance(label, Literal) and label.language:
            labels[label.language] = str(label)
        else:
            labels["default"] = str(label)

    # Select appropriate label
    if lang in labels:
        info["label"] = labels[lang]
    elif "en" in labels:
        info["label"] = labels["en"]
    elif "default" in labels:
        info["label"] = labels["default"]
    elif labels:
        # Take any available label
        info["label"] = next(iter(labels.values()))

    # Get type
    for node_type in g.objects(node_uri, RDF.type):
        if str(node_type).startswith(str(MYMATH)):
            info["type"] = str(node_type).replace(str(MYMATH), "")
            break

    return info


def get_local_neighborhood(g: Graph, node_id: str) -> Tuple[Set[str], Set[Tuple[str, str, str]]]:
    """
    Get the local neighborhood of a node (dependencies and dependents).
    Returns (nodes, edges) where edges are tuples of (source_id, target_id, relation).
    """
    node_uri = BASE[node_id]
    nodes = {node_id}
    edges = set()

    # Get dependencies (nodes this node uses)
    for dep in g.objects(node_uri, MYMATH.uses):
        dep_id = str(dep).replace(BASE_URI, "")
        nodes.add(dep_id)
        edges.add((node_id, dep_id, "uses"))

    # Get dependents (nodes that use this node)
    for dependent in g.subjects(MYMATH.uses, node_uri):
        dep_id = str(dependent).replace(BASE_URI, "")
        nodes.add(dep_id)
        edges.add((dep_id, node_id, "uses"))

    # Get examples
    for example in g.objects(node_uri, MYMATH.hasExample):
        ex_id = str(example).replace(BASE_URI, "")
        nodes.add(ex_id)
        edges.add((node_id, ex_id, "hasExample"))

    for concept in g.subjects(MYMATH.hasExample, node_uri):
        concept_id = str(concept).replace(BASE_URI, "")
        nodes.add(concept_id)
        edges.add((concept_id, node_id, "hasExample"))

    return nodes, edges


def get_node_style(node_type: str) -> str:
    """Get Mermaid style for a node based on its type."""
    styles = {
        "Definition": ":::definition",
        "Theorem": ":::theorem",
        "Lemma": ":::theorem",
        "Proposition": ":::theorem",
        "Corollary": ":::theorem",
        "Axiom": ":::axiom",
        "Example": ":::example",
    }
    return styles.get(node_type, "")


def generate_mermaid_diagram(
    g: Graph,
    node_id: str,
    lang: str = "en",
    max_nodes: int = 20,
    lean_mappings: Optional[Dict[str, Any]] = None,
    lean_validation: Optional[Dict[str, Any]] = None,
) -> str:
    """Generate Mermaid diagram for a node's neighborhood with language support."""
    nodes, edges = get_local_neighborhood(g, node_id)

    # Limit the number of nodes for readability
    if len(nodes) > max_nodes:
        # Prioritize showing direct dependencies and a few dependents
        # This is a simple heuristic - could be improved
        nodes_to_keep = {node_id}
        for src, tgt, _ in edges:
            if src == node_id:
                nodes_to_keep.add(tgt)
            if len(nodes_to_keep) >= max_nodes:
                break
        nodes = nodes_to_keep
        edges = {e for e in edges if e[0] in nodes and e[1] in nodes}

    # Build node info with language preference
    node_info = {}
    for n in nodes:
        info = get_node_info(g, BASE[n], lang)
        node_info[n] = info

        # Add proof status if available
        if lean_mappings and lean_validation and n in lean_mappings:
            proof_status = lean_validation.get(n, "not_implemented")
            info["proof_status"] = proof_status

    # Generate Mermaid code
    lines = ["graph TD"]

    # Add class definitions for styling
    lines.extend(
        [
            "    classDef definition fill:#e1f5fe,stroke:#01579b,stroke-width:2px",
            "    classDef theorem fill:#f3e5f5,stroke:#4a148c,stroke-width:2px",
            "    classDef axiom fill:#fff3e0,stroke:#e65100,stroke-width:2px",
            "    classDef example fill:#e8f5e9,stroke:#1b5e20,stroke-width:2px",
            "    classDef current fill:#ffebee,stroke:#b71c1c,stroke-width:3px",
        ]
    )

    # Proof status icons
    proof_status_icons = {
        "completed": "✅",
        "warnings_present": "⚠️",
        "errors_present": "❌",
        "not_implemented": "📝",
    }

    # Add nodes
    for n_id, info in node_info.items():
        label = info["label"] or n_id
        # Escape special characters
        label = label.replace('"', "&quot;")

        # Add proof status icon if available
        if "proof_status" in info and info["proof_status"] in proof_status_icons:
            label = f"{label} {proof_status_icons[info['proof_status']]}"

        node_type = info["type"] or "Unknown"
        style_class = get_node_style(node_type)

        # Format node
        node_def = f'    {n_id}["{label}"]'
        if style_class:
            lines.append(node_def + style_class)
        else:
            lines.append(node_def)

    # Add edges
    for src, tgt, rel in edges:
        if src in nodes and tgt in nodes:
            if rel == "uses":
                lines.append(f"    {src} --> {tgt}")
            elif rel == "hasExample":
                lines.append(f"    {src} -.->|example| {tgt}")

    # Highlight the current node
    lines.append(f"    class {node_id} current")

    return "\n".join(lines)


def generate_all_diagrams(ttl_file: Path, output_dir: Path) -> None:
    """Generate Mermaid diagrams for all nodes."""
    g = load_knowledge_graph(ttl_file)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Load Lean data
    lean_mappings, lean_validation = load_lean_data()

    # Get all nodes
    nodes = set()
    for s in g.subjects(RDF.type, None):
        if str(s).startswith(BASE_URI):
            node_id = str(s).replace(BASE_URI, "")
            nodes.add(node_id)

    print(f"Generating Mermaid diagrams for {len(nodes)} nodes...")

    # Track statistics
    stats = {"total": len(nodes), "generated": 0, "skipped": 0}

    # Generate diagrams for each language
    for lang in ["en", "ja"]:
        lang_dir = output_dir / lang
        lang_dir.mkdir(parents=True, exist_ok=True)
        lang_generated = 0
        lang_skipped = 0

        # Generate diagram for each node
        for node_id in sorted(nodes):
            # Get neighborhood to check if diagram will have content
            local_nodes, local_edges = get_local_neighborhood(g, node_id)

            # Skip if node has no connections (only itself in the neighborhood)
            if len(local_nodes) <= 1 or len(local_edges) == 0:
                lang_skipped += 1
                continue

            diagram = generate_mermaid_diagram(
                g, node_id, lang=lang, lean_mappings=lean_mappings, lean_validation=lean_validation
            )

            # Additional validation: check if diagram has meaningful content
            # (not just class definitions and a single node)
            if diagram and len(diagram.strip()) > 0:
                output_file = lang_dir / f"{node_id}.mermaid"
                with open(output_file, "w", encoding="utf-8") as f:
                    f.write(diagram)
                lang_generated += 1
            else:
                lang_skipped += 1

        print(
            f"Generated {lang_generated} Mermaid diagrams for {lang} in {lang_dir} "
            f"(skipped {lang_skipped} isolated nodes)"
        )

        if lang == "en":  # Count only once
            stats["generated"] = lang_generated
            stats["skipped"] = lang_skipped

    # Also generate a JSON index for easy lookup
    index = {"nodes": list(sorted(nodes)), "generated": True, "stats": stats}

    with open(output_dir / "index.json", "w", encoding="utf-8") as f:
        json.dump(index, f, indent=2)


def insert_diagrams_in_content() -> None:
    """Insert Mermaid diagrams into Quarto content files."""
    content_dir = Path("content")
    diagrams_dir = Path("output/mermaid")

    if not diagrams_dir.exists():
        print("No diagrams found. Run generate_all_diagrams first.")
        return

    # Process each .qmd file
    for qmd_file in content_dir.rglob("*.qmd"):
        with open(qmd_file, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)

        if "id" not in post.metadata:
            continue

        node_id = post.metadata["id"]
        diagram_file = diagrams_dir / f"{node_id}.mermaid"

        if not diagram_file.exists():
            continue

        # Check if diagram is already in content
        if "## Dependency Graph" in post.content:
            print(f"Diagram already exists in {qmd_file}")
            continue

        # Read diagram
        with open(diagram_file, "r", encoding="utf-8") as f:
            diagram_content = f.read()

        # Add diagram section to content
        new_content = post.content + "\n\n## Dependency Graph\n\n" + diagram_content

        # Write back
        post.content = new_content
        with open(qmd_file, "w", encoding="utf-8") as f:
            f.write(frontmatter.dumps(post))

        print(f"Added diagram to {qmd_file}")


def main() -> None:
    """Main function."""
    ttl_file = Path("knowledge_graph.ttl")
    output_dir = Path("output/mermaid")

    if not ttl_file.exists():
        print(f"Error: {ttl_file} not found. Run build_graph.py first.")
        return

    # Generate all diagrams
    generate_all_diagrams(ttl_file, output_dir)

    # Optionally insert into content files
    # Uncomment the following line to automatically insert diagrams
    # insert_diagrams_in_content()


if __name__ == "__main__":
    main()
