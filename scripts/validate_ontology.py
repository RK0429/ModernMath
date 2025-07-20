#!/usr/bin/env python3
"""
Validate the mathematical ontology for syntax and consistency.
"""

import sys
from pathlib import Path
from rdflib import Graph, Namespace, RDF, RDFS, OWL

# from rdflib.namespace import SKOS, DC, DCTERMS  # For future use


def validate_ontology(ontology_path: Path) -> bool:
    """Validate the ontology file for syntax and basic consistency."""
    print(f"Validating ontology: {ontology_path}")

    try:
        # Load the ontology
        g = Graph()
        g.parse(ontology_path, format="turtle")
        print(f"✓ Successfully parsed ontology ({len(g)} triples)")

        # Define namespaces
        MYMATH = Namespace("https://mathwiki.org/ontology#")

        # Check for required classes
        required_classes = [
            (MYMATH.Axiom, "Axiom"),
            (MYMATH.Definition, "Definition"),
            (MYMATH.Theorem, "Theorem"),
            (MYMATH.Example, "Example"),
            (MYMATH.MathematicalStatement, "Mathematical Statement"),
        ]

        print("\nChecking required classes:")
        for class_uri, class_name in required_classes:
            if (class_uri, RDF.type, RDFS.Class) in g:
                print(f"  ✓ {class_name} class found")
            else:
                print(f"  ✗ {class_name} class missing")
                return False

        # Check for required properties
        required_properties = [
            (MYMATH.uses, "uses"),
            (MYMATH.hasExample, "hasExample"),
            (MYMATH.generalizes, "generalizes"),
            (MYMATH.implies, "implies"),
            (MYMATH.hasDomain, "hasDomain"),
        ]

        print("\nChecking required properties:")
        for prop_uri, prop_name in required_properties:
            if (prop_uri, RDF.type, RDF.Property) in g:
                print(f"  ✓ {prop_name} property found")
            else:
                print(f"  ✗ {prop_name} property missing")
                return False

        # Check for duplicate definitions
        print("\nChecking for duplicate definitions:")
        all_subjects = set()
        duplicates = []

        for s, p, o in g:
            if p == RDF.type and (o == RDFS.Class or o == RDF.Property):
                if s in all_subjects:
                    duplicates.append(s)
                all_subjects.add(s)

        if duplicates:
            print(f"  ✗ Found duplicate definitions: {duplicates}")
            return False
        else:
            print("  ✓ No duplicate definitions found")

        # Check namespace declarations
        print("\nChecking namespace usage:")
        namespaces_used = set()
        for s, p, o in g:
            for term in [s, p, o]:
                if hasattr(term, "n3"):
                    ns_match = term.n3().split(":")[0] if ":" in term.n3() else None
                    if ns_match:
                        namespaces_used.add(ns_match.strip("<>"))

        print(f"  Namespaces used: {', '.join(sorted(namespaces_used))}")

        # Validate inverse properties
        print("\nChecking inverse properties:")
        inverse_pairs = [
            (MYMATH.hasExample, MYMATH.isExampleOf),
            (MYMATH.generalizes, MYMATH.specializes),
            (MYMATH.hasProof, MYMATH.proves),
        ]

        for prop1, prop2 in inverse_pairs:
            if (prop1, OWL.inverseOf, prop2) in g or (prop2, OWL.inverseOf, prop1) in g:
                prop1_name = prop1.split("#")[-1]
                prop2_name = prop2.split("#")[-1]
                print(f"  ✓ {prop1_name} ↔ {prop2_name} inverse relationship found")
            else:
                prop1_name = prop1.split("#")[-1]
                prop2_name = prop2.split("#")[-1]
                print(
                    f"  ⚠ {prop1_name} ↔ {prop2_name} inverse relationship " "not properly defined"
                )

        # Summary statistics
        print("\nOntology Statistics:")
        classes = list(g.subjects(RDF.type, RDFS.Class))
        properties = list(g.subjects(RDF.type, RDF.Property))
        print(f"  Total triples: {len(g)}")
        print(f"  Classes: {len(classes)}")
        print(f"  Properties: {len(properties)}")

        print("\n✅ Ontology validation successful!")
        return True

    except Exception as e:
        print("\n❌ Ontology validation failed:")
        print(f"  Error: {e}")
        return False


def main() -> None:
    """Main function."""
    ontology_path = Path("ontology/math-ontology.ttl")

    if not ontology_path.exists():
        print(f"Error: Ontology file not found at {ontology_path}")
        sys.exit(1)

    if validate_ontology(ontology_path):
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
