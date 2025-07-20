#!/usr/bin/env python3
"""
Test the LLM PR review functionality without creating an actual PR.
"""

import sys
from pathlib import Path
from llm_integration import MathKnowledgeGraphLLM

def test_llm_pr_review():
    """Test the LLM PR review functionality with sample content."""
    
    # Create test content that should trigger suggestions
    test_files = [
        ("content/test/def-test-concept.qmd", """---
title: "Definition: Test Concept"
id: "def-test-concept"
type: "Definition"
status: "draft"
---

# Definition: Test Concept {#def-test-concept}

A test concept is a mathematical object that demonstrates the following properties:

1. It forms a group under the standard operation
2. The topology on this space is compact
3. Any continuous function from this space to itself has a fixed point

This concept is closely related to the notion of a vector space and shares many 
properties with metric spaces. The fundamental theorem of arithmetic applies to 
certain decompositions of test concepts.

## Properties

When considering a test concept, we often need to verify:
- The axiom of choice is not required for basic constructions
- The limit of any convergent sequence exists
- Every subgroup of finite index contains the identity element

## Examples

Common examples include:
- The ring of integers modulo n
- Any field of characteristic zero
- The category of sets with morphisms as functions
"""),
        ("content/test/thm-test-theorem.qmd", """---
title: "Theorem: Test Result"
id: "thm-test-result"
type: "Theorem"
status: "draft"
requires:
  - "def-test-concept"
---

# Theorem: Test Result {#thm-test-result}

Let X be a test concept as defined in @def-test-concept. Then:

1. Every prime number divides the order of X
2. The derivative of any smooth function on X exists
3. Cantor's theorem applies to the power set of X

## Proof

The proof follows from the intermediate value theorem and uses the following lemmas:
- The kernel of any homomorphism is a normal subgroup
- Linear transformations preserve the basis structure
- The binomial coefficient formula holds

By Lagrange's theorem, we know the order divides the group order.
The Heine-Borel theorem ensures compactness is preserved.

## Applications

This result has applications in:
- Probability spaces and random variables
- Natural transformations between functors
- Euclidean spaces with the standard metric
""")
    ]
    
    # Initialize LLM
    llm = MathKnowledgeGraphLLM()
    
    # Analyze the test files
    print("Testing LLM PR review functionality...")
    print("=" * 60)
    
    result = llm.analyze_pull_request(test_files)
    
    # Print results
    print(f"\nAnalysis Summary:")
    print(f"- Total files analyzed: {result['total_files']}")
    print(f"- Files with suggestions: {result['files_with_suggestions']}")
    print(f"- Total suggestions: {len(result['suggestions'])}")
    
    if result['suggestions']:
        print("\nDetailed Suggestions:")
        print("-" * 60)
        
        # Group by file
        by_file = {}
        for suggestion in result['suggestions']:
            file = suggestion['file']
            if file not in by_file:
                by_file[file] = []
            by_file[file].append(suggestion)
        
        for file, suggestions in by_file.items():
            print(f"\n📄 {file}")
            for s in suggestions:
                print(f"  • Suggest linking to: @{s['target']} (confidence: {s['confidence']:.0%})")
                if s['evidence']:
                    evidence = s['evidence'].replace('\n', ' ').strip()
                    if len(evidence) > 80:
                        evidence = evidence[:80] + "..."
                    print(f"    Context: \"{evidence}\"")
                print()
    
    # Test the PR comment formatting
    print("\nFormatted PR Comment:")
    print("=" * 60)
    
    comment = "## 🤖 Mathematical Content Review\n\n"
    
    if not result['suggestions']:
        comment += "✅ No missing cross-references detected in the changed files.\n"
    else:
        comment += "### 📝 Suggested Cross-References\n\n"
        comment += "The following mathematical concepts appear to be mentioned but not linked:\n\n"
        
        for file, suggestions in by_file.items():
            comment += f"**`{file}`**\n"
            for s in suggestions:
                comment += f"- Consider linking to `@{s['target']}` "
                comment += f"(confidence: {s['confidence']:.0%})\n"
                if s['evidence']:
                    evidence = s['evidence'].replace('\n', ' ').strip()
                    if len(evidence) > 100:
                        evidence = evidence[:100] + "..."
                    comment += f"  > Context: *{evidence}*\n"
            comment += "\n"
    
    comment += "\n---\n"
    comment += "*This is an automated review. Please verify suggestions before applying them.*\n"
    
    print(comment)
    
    return len(result['suggestions']) > 0

def main():
    """Main function."""
    print("LLM PR Review Test")
    print("==================\n")
    
    has_suggestions = test_llm_pr_review()
    
    if has_suggestions:
        print("\n✅ Test passed: LLM correctly identified missing cross-references")
    else:
        print("\n⚠️  Test completed but no suggestions were found")
    
    print("\nNote: This is a simulation. In a real PR, the workflow would:")
    print("1. Detect changed .qmd files")
    print("2. Analyze them for missing cross-references")
    print("3. Post suggestions as a PR comment")
    print("4. Update the comment if files change")

if __name__ == "__main__":
    main()