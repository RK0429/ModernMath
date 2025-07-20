# Content Authoring Tutorial

This tutorial will guide you through adding new mathematical content to the Mathematics Knowledge Graph Wiki.

## Prerequisites

- Basic knowledge of Markdown
- Familiarity with LaTeX for mathematical notation
- Understanding of the mathematical concept you want to add

## Overview

Each mathematical concept in our wiki is:
1. Written as a Quarto Markdown (`.qmd`) file
2. Structured with semantic metadata
3. Connected to related concepts through cross-references
4. Automatically integrated into the knowledge graph

## Step-by-Step Guide

### Step 1: Determine the Content Type

First, identify what type of content you're adding:

- **Definition**: A formal mathematical definition
- **Theorem**: A proven statement (includes lemmas, propositions, corollaries)
- **Axiom**: A foundational assumption
- **Example**: A concrete instance or illustration

### Step 2: Choose the Right Location

Navigate to the appropriate domain folder in `content/`:

```
content/
├── algebra/           # Groups, rings, fields, vector spaces
├── analysis/          # Limits, derivatives, integrals
├── topology/          # Open sets, continuity, compactness
├── geometry/          # Euclidean spaces, metrics
├── number-theory/     # Primes, divisibility
├── combinatorics/     # Permutations, combinations
├── logic-set-theory/  # Sets, logic, axioms
├── probability-statistics/  # Probability spaces, distributions
└── category-theory/   # Categories, functors
```

### Step 3: Create the File

Use the naming convention:
- Definitions: `def-<name>.qmd`
- Theorems: `thm-<name>.qmd`
- Examples: `ex-<name>.qmd`
- Axioms: `ax-<name>.qmd`

Use kebab-case (lowercase with hyphens) for the name.

### Step 4: Add Required Metadata

Start your file with YAML front matter:

```yaml
---
title: "Definition: Prime Number"
id: "def-prime"
type: "Definition"
status: "complete"
requires:
  - "def-natural-number"
  - "def-divisibility"
---
```

#### Metadata Fields Explained:

- **title**: Human-readable title (format: "Type: Name")
- **id**: Unique identifier matching the filename (without .qmd)
- **type**: One of: Definition, Theorem, Axiom, Example
- **status**: One of:
  - `stub`: Placeholder with minimal content
  - `draft`: Work in progress
  - `complete`: Ready for use
  - `verified`: Formally verified with Lean
- **requires**: List of IDs this concept depends on (optional)

### Step 5: Write the Content

#### Opening Statement

Start with a clear, concise statement:

```markdown
A **prime number** is a natural number greater than 1 that has no positive divisors other than 1 and itself.
```

#### Mathematical Notation

Use LaTeX for all mathematical expressions:

```markdown
Formally, a natural number $p > 1$ is prime if and only if:

$$
\forall a, b \in \mathbb{N}: p = ab \implies (a = 1 \land b = p) \lor (a = p \land b = 1)
$$
```

#### Cross-References

Link to related concepts using `@` syntax:

```markdown
Every natural number greater than 1 is either prime or can be expressed as a product of primes (see @thm-fundamental-arithmetic).

The concept of primality depends on @def-divisibility in the natural numbers.
```

### Step 6: Add Examples (for Definitions)

Include clarifying examples:

```markdown
## Examples

- 2, 3, 5, 7, 11 are the first five prime numbers
- 4 is not prime because $4 = 2 \times 2$
- 1 is not considered prime by modern convention
```

### Step 7: Add Related Concepts

Link to examples, theorems, or applications:

```markdown
## Related Concepts

- See @ex-sieve-eratosthenes for an algorithm to find primes
- The distribution of primes is described by @thm-prime-number-theorem
- For the fundamental role of primes, see @thm-fundamental-arithmetic
```

### Step 8: Validate Your Content

Before committing, validate your file:

```bash
# Validate metadata structure
poetry run python scripts/validate_metadata.py

# Check that all cross-references exist
poetry run python scripts/validate_graph.py
```

## Complete Example

Here's a complete example file (`content/number-theory/def-prime.qmd`):

```markdown
---
title: "Definition: Prime Number"
id: "def-prime"
type: "Definition"
status: "complete"
requires:
  - "def-natural-number"
  - "def-divisibility"
---

A **prime number** is a @def-natural-number greater than 1 that has no positive divisors other than 1 and itself.

## Formal Definition

Let $p \in \mathbb{N}$ with $p > 1$. We say $p$ is **prime** if and only if:

$$
\forall a \in \mathbb{N}: a \mid p \implies a = 1 \lor a = p
$$

where $a \mid p$ denotes that $a$ divides $p$ (see @def-divisibility).

## Examples

The first few prime numbers are:
- 2 (the only even prime)
- 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, ...

Non-examples:
- 1 is not prime (by convention)
- 4 = 2 × 2 is not prime
- 6 = 2 × 3 is not prime

## Properties

1. **Infinitude**: There are infinitely many primes (@thm-euclid-primes)
2. **Fundamental Theorem**: Every natural number > 1 has a unique prime factorization (@thm-fundamental-arithmetic)
3. **Distribution**: The density of primes decreases logarithmically (@thm-prime-number-theorem)

## Related Concepts

- @def-composite: Numbers that are not prime
- @thm-wilson: A characterization of primes
- @ex-sieve-eratosthenes: Algorithm for finding primes
```

## Building and Testing

After adding content:

1. **Rebuild the knowledge graph**:
   ```bash
   poetry run python scripts/build_graph.py
   ```

2. **Generate visualizations**:
   ```bash
   poetry run python scripts/generate_pyvis.py
   ```

3. **Preview locally**:
   ```bash
   quarto preview
   ```

4. **Check your node's graph**:
   Navigate to `/output/interactive/def-prime.html` to see the interactive visualization

## Best Practices

### Do's:
- ✅ Keep definitions concise and precise
- ✅ Use standard mathematical notation
- ✅ Link to all referenced concepts
- ✅ Provide illustrative examples
- ✅ Include both formal and intuitive explanations

### Don'ts:
- ❌ Don't duplicate existing content
- ❌ Don't use ambiguous notation
- ❌ Don't forget to validate metadata
- ❌ Don't include proofs in definition files (create separate theorem files)

## Common Issues and Solutions

### Issue: Cross-reference not found
**Solution**: Ensure the referenced file exists and has the correct ID in its metadata

### Issue: LaTeX not rendering
**Solution**: Check for syntax errors, ensure you're using `$` for inline and `$$` for display math

### Issue: File in wrong location
**Solution**: Move to the correct domain folder and update any existing references

## Getting Help

- Review existing content for examples
- Check the [style guide](style-guide.md)
- Consult the [CONTRIBUTING.md](../CONTRIBUTING.md) guide
- Open an issue for questions

## Next Steps

After mastering basic content creation:

1. Learn about [formal verification with Lean](lean-integration.md)
2. Explore [advanced cross-referencing](advanced-authoring.md)
3. Contribute to [improving existing content](content-improvement.md)

Happy authoring! Your contributions help build a comprehensive, interconnected map of mathematical knowledge.