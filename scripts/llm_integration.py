"""
LLM Integration Module for Math Knowledge Graph
Provides an abstraction layer for working with different LLM providers
"""

import json
import logging
from typing import List, Dict, Optional, Any, Tuple
from abc import ABC, abstractmethod
from dataclasses import dataclass
import re
from pathlib import Path

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class MathConcept:
    """Represents a mathematical concept extracted from text"""

    name: str
    type: str  # Definition, Theorem, Axiom, Example
    references: List[str]  # Other concepts referenced
    confidence: float


@dataclass
class RelationshipSuggestion:
    """Represents a suggested relationship between concepts"""

    source: str
    target: str
    relationship_type: str  # uses, hasExample, generalizes, implies
    confidence: float
    evidence: str  # Text snippet supporting this relationship


class LLMProvider(ABC):
    """Abstract base class for LLM providers"""

    @abstractmethod
    def extract_concepts(self, text: str) -> List[MathConcept]:
        """Extract mathematical concepts from text"""
        pass

    @abstractmethod
    def suggest_relationships(
        self, text: str, existing_links: List[str]
    ) -> List[RelationshipSuggestion]:
        """Suggest missing relationships based on text analysis"""
        pass

    @abstractmethod
    def generate_content(self, node_type: str, title: str, context: Dict[str, Any]) -> str:
        """Generate content for a new node"""
        pass

    @abstractmethod
    def check_consistency(
        self, node_data: Dict[str, Any], graph_context: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Check consistency of node content with graph context"""
        pass


class MockLLMProvider(LLMProvider):
    """Mock LLM provider for testing and development"""

    def extract_concepts(self, text: str) -> List[MathConcept]:
        """Extract mathematical concepts using pattern matching"""
        concepts = []

        # Pattern for definitions
        def_pattern = r"\b(?:definition of|define[sd]?|Definition:)\s+(\w+(?:\s+\w+)*)"
        for match in re.finditer(def_pattern, text, re.IGNORECASE):
            concepts.append(
                MathConcept(
                    name=match.group(1).strip(), type="Definition", references=[], confidence=0.8
                )
            )

        # Pattern for theorems
        thm_pattern = r"\b(?:theorem|lemma|proposition|corollary)\s+(?:of\s+)?(\w+(?:\s+\w+)*)"
        for match in re.finditer(thm_pattern, text, re.IGNORECASE):
            concepts.append(
                MathConcept(
                    name=match.group(1).strip(), type="Theorem", references=[], confidence=0.7
                )
            )

        # Extract referenced concepts
        ref_pattern = r"(?:uses?|depends?\s+on|requires?|assumes?)\s+(?:the\s+)?(\w+(?:\s+\w+)*)"
        references = []
        for match in re.finditer(ref_pattern, text, re.IGNORECASE):
            references.append(match.group(1).strip())

        # Add references to concepts
        for concept in concepts:
            concept.references = references

        return concepts

    def suggest_relationships(
        self, text: str, existing_links: List[str]
    ) -> List[RelationshipSuggestion]:
        """Suggest relationships based on text patterns"""
        suggestions = []

        # Extract concepts mentioned in text
        # concept_pattern = r"@(\w+(?:-\w+)*)"
        # For future use: re.findall(concept_pattern, text)

        # Find concepts that are mentioned but not linked
        text_lower = text.lower()
        common_concepts = [
            ("group", "def-group"),
            ("set", "def-set"),
            ("binary operation", "def-binary-operation"),
            ("topological space", "def-topological-space"),
            ("continuous", "def-continuity"),
            ("compact", "def-compact"),
        ]

        for concept_text, concept_id in common_concepts:
            if concept_text in text_lower and concept_id not in existing_links:
                # Try to find the context
                idx = text_lower.find(concept_text)
                start = max(0, idx - 50)
                end = min(len(text), idx + len(concept_text) + 50)
                evidence = text[start:end].strip()

                suggestions.append(
                    RelationshipSuggestion(
                        source="current_node",
                        target=concept_id,
                        relationship_type="uses",
                        confidence=0.7,
                        evidence=evidence,
                    )
                )

        return suggestions

    def generate_content(self, node_type: str, title: str, context: Dict[str, Any]) -> str:
        """Generate template content for a new node"""
        templates = {
            "Definition": """---
title: "{title}"
id: "{node_id}"
type: "Definition"
status: "draft"
requires: []
---

# {title}

## Definition

[TODO: Add formal definition here]

## Intuition

[TODO: Add intuitive explanation]

## Properties

[TODO: List key properties]

## Examples

[TODO: Link to examples]

## Related Concepts

[TODO: Link to related concepts]
""",
            "Theorem": """---
title: "{title}"
id: "{node_id}"
type: "Theorem"
status: "draft"
requires: []
---

# {title}

## Statement

[TODO: Add formal statement]

## Proof

[TODO: Add proof or link to proof]

## Applications

[TODO: Describe applications]

## Related Results

[TODO: Link to related theorems]
""",
            "Example": """---
title: "{title}"
id: "{node_id}"
type: "Example"
status: "draft"
requires: []
---

# {title}

## Description

[TODO: Describe the example]

## Construction

[TODO: Show how to construct this example]

## Properties

[TODO: List properties this example satisfies]

## Illustrates

[TODO: Link to concepts this example illustrates]
""",
        }

        node_id = title.lower().replace(" ", "-").replace(":", "")
        if not node_id.startswith(("def-", "thm-", "ex-", "ax-")):
            prefix_map = {"Definition": "def-", "Theorem": "thm-", "Example": "ex-", "Axiom": "ax-"}
            node_id = prefix_map.get(node_type, "") + node_id

        template = templates.get(node_type, templates["Definition"])
        return template.format(title=title, node_id=node_id)

    def check_consistency(
        self, node_data: Dict[str, Any], graph_context: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Basic consistency checks"""
        issues = []
        warnings = []

        # Check if all required fields are present
        required_fields = ["title", "id", "type"]
        for field in required_fields:
            if field not in node_data:
                issues.append(f"Missing required field: {field}")

        # Check if references exist
        if "requires" in node_data:
            existing_nodes = graph_context.get("existing_nodes", [])
            for ref in node_data["requires"]:
                if ref not in existing_nodes:
                    warnings.append(f"Referenced node '{ref}' not found in graph")

        # Check for circular dependencies
        if "id" in node_data and "dependencies" in graph_context:
            node_id = node_data["id"]
            deps = graph_context["dependencies"].get(node_id, [])
            if node_id in deps:
                issues.append(f"Circular dependency detected for node '{node_id}'")

        return {"issues": issues, "warnings": warnings, "valid": len(issues) == 0}


class MathKnowledgeGraphLLM:
    """Main class for LLM integration with the knowledge graph"""

    def __init__(self, provider: Optional[LLMProvider] = None):
        self.provider = provider or MockLLMProvider()
        self.logger = logging.getLogger(__name__)

    def analyze_pull_request(self, changed_files: List[Tuple[str, str]]) -> Dict[str, Any]:
        """Analyze changed files in a pull request for missing links"""
        all_suggestions = []

        for filepath, content in changed_files:
            # Skip non-content files
            if not filepath.endswith(".qmd") or "/content/" not in filepath:
                continue

            # Extract existing links
            existing_links = re.findall(r"@(\w+(?:-\w+)*)", content)

            # Get suggestions
            suggestions = self.provider.suggest_relationships(content, existing_links)

            for suggestion in suggestions:
                suggestion_dict = {
                    "file": filepath,
                    "target": suggestion.target,
                    "type": suggestion.relationship_type,
                    "confidence": suggestion.confidence,
                    "evidence": suggestion.evidence,
                }
                all_suggestions.append(suggestion_dict)

        return {
            "suggestions": all_suggestions,
            "total_files": len(changed_files),
            "files_with_suggestions": len(set(s["file"] for s in all_suggestions)),
        }

    def generate_draft_content(
        self, node_type: str, title: str, related_concepts: Optional[List[str]] = None
    ) -> str:
        """Generate draft content for a new mathematical concept"""
        context = {"related_concepts": related_concepts or []}

        content = self.provider.generate_content(node_type, title, context)

        # If related concepts provided, add them to requires
        if related_concepts:
            lines = content.split("\n")
            for i, line in enumerate(lines):
                if line.startswith("requires:"):
                    # Add related concepts to requires
                    requires_line = f"requires: {json.dumps(related_concepts)}"
                    lines[i] = requires_line
                    break
            content = "\n".join(lines)

        return content

    def validate_node_content(self, node_path: Path, graph_data: Dict[str, Any]) -> Dict[str, Any]:
        """Validate node content against the knowledge graph"""
        import frontmatter

        with open(node_path, "r", encoding="utf-8") as f:
            post = frontmatter.load(f)

        node_data = post.metadata

        # Get existing nodes from graph
        existing_nodes = list(graph_data.get("nodes", {}).keys())

        # Get dependencies for circular check
        dependencies = {}
        for node_id, node_info in graph_data.get("nodes", {}).items():
            deps = node_info.get("dependencies", [])
            dependencies[node_id] = deps

        graph_context = {"existing_nodes": existing_nodes, "dependencies": dependencies}

        return self.provider.check_consistency(node_data, graph_context)

    def extract_concepts_from_text(self, text: str) -> List[Dict[str, Any]]:
        """Extract mathematical concepts from natural language text"""
        concepts = self.provider.extract_concepts(text)

        return [
            {"name": c.name, "type": c.type, "references": c.references, "confidence": c.confidence}
            for c in concepts
        ]


# CLI interface for testing
if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="LLM Integration for Math Knowledge Graph")
    parser.add_argument(
        "command", choices=["extract", "generate", "validate", "analyze"], help="Command to execute"
    )
    parser.add_argument("--input", "-i", help="Input file or text")
    parser.add_argument("--type", "-t", help="Node type (for generate command)")
    parser.add_argument("--title", help="Node title (for generate command)")
    parser.add_argument("--graph", "-g", help="Graph data file (for validate command)")

    args = parser.parse_args()

    llm = MathKnowledgeGraphLLM()

    if args.command == "extract":
        if args.input:
            if Path(args.input).exists():
                with open(args.input, "r") as f:
                    text = f.read()
            else:
                text = args.input

            concepts = llm.extract_concepts_from_text(text)
            print(json.dumps(concepts, indent=2))

    elif args.command == "generate":
        if args.type and args.title:
            content = llm.generate_draft_content(args.type, args.title)
            print(content)
        else:
            print("Error: --type and --title required for generate command")

    elif args.command == "validate":
        if args.input and args.graph:
            with open(args.graph, "r") as f:
                graph_data = json.load(f)

            result = llm.validate_node_content(Path(args.input), graph_data)
            print(json.dumps(result, indent=2))
        else:
            print("Error: --input and --graph required for validate command")
