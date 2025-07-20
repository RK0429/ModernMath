# Math Knowledge Graph Wiki - Content Authoring Style Guide

## Overview

This style guide provides comprehensive guidelines for authoring mathematical content in the Math Knowledge Graph Wiki. Following these conventions ensures consistency, maintainability, and proper integration with the automated knowledge graph extraction pipeline.

## File Organization

### Directory Structure

All content must be organized within the appropriate subject-specific directories:

- `content/algebra/`
- `content/analysis/`
- `content/geometry/`
- `content/topology/`
- `content/number-theory/`
- `content/combinatorics/`
- `content/logic-set-theory/`
- `content/probability-statistics/`
- `content/category-theory/`

Each directory contains a `_metadata.yml` file that automatically applies domain classification to all files within that directory.

### File Naming Conventions

Files must follow a consistent naming pattern:

- **Definitions**: `def-[concept-name].qmd` (e.g., `def-group.qmd`)
- **Theorems**: `thm-[theorem-name].qmd` (e.g., `thm-pythagorean.qmd`)
- **Axioms**: `ax-[axiom-name].qmd` (e.g., `ax-choice.qmd`)
- **Examples**: `ex-[example-name].qmd` (e.g., `ex-integers-addition.qmd`)
- **Lemmas**: `lem-[lemma-name].qmd`
- **Propositions**: `prop-[proposition-name].qmd`
- **Corollaries**: `cor-[corollary-name].qmd`

Use lowercase letters and hyphens to separate words. Avoid underscores and special characters.

## YAML Front Matter Requirements

Every `.qmd` file must include a properly formatted YAML front matter section with the following required fields:

```yaml
---
title: "Definition: Group"
id: "def-group"
type: "Definition"
status: "complete"
---
```

### Required Fields

| Field | Type | Description | Valid Values |
|-------|------|-------------|--------------|
| `title` | String | Human-readable title | Should follow format "Type: Name" |
| `id` | String | Unique identifier | Must match the cross-reference label |
| `type` | String | Node type in the ontology | Definition, Theorem, Axiom, Example, Lemma, Proposition, Corollary |
| `status` | String | Content maturity level | stub, draft, complete, verified |

### Optional Fields

| Field | Type | Description | Example |
|-------|------|-------------|---------|
| `lean_id` | String | Lean library identifier | `Mathlib.GroupTheory.Group.group` |
| `requires` | Array | Explicit dependencies | `["def-set", "def-binary-operation"]` |
| `author` | String | Content author | `John Doe` |
| `date_created` | Date | Creation date | `2025-01-20` |
| `date_modified` | Date | Last modification | `2025-01-20` |

### Complete Example

```yaml
---
title: "Theorem: Lagrange's Theorem"
id: "thm-lagrange"
type: "Theorem"
status: "complete"
lean_id: "Mathlib.GroupTheory.Lagrange"
requires:
  - "def-group"
  - "def-subgroup"
  - "def-order"
author: "Math KG Team"
date_created: "2025-01-20"
---
```

## Cross-Reference Conventions

### The Golden Rule

**Always use the `@` syntax when referencing other mathematical concepts in your content.**

This is the most critical convention for building the knowledge graph. Every reference to another definition, theorem, axiom, or example must use Quarto's cross-reference syntax.

### Correct Usage

```markdown
By @def-group, we know that the identity element is unique.

This follows from @thm-lagrange and @def-subgroup.

See @ex-integers-addition for a concrete example.
```

### Cross-Reference Labels

- The label in `@label` must match the `id` field in the target file's YAML front matter
- Labels should be descriptive and follow the same pattern as file names
- Use hyphens to separate words in labels

### Linking Across Directories

When referencing content in different directories, still use the simple `@label` syntax. The build system will resolve these references automatically.

## Mathematical Notation

### LaTeX Usage

Use LaTeX for all mathematical expressions:

- Inline math: `$G$` or `$x \in \mathbb{R}$`
- Display math:
  ```markdown
  $$
  \sum_{i=1}^{n} i = \frac{n(n+1)}{2}
  $$
  ```

### Common Notation Standards

- Sets: `\mathbb{N}`, `\mathbb{Z}`, `\mathbb{Q}`, `\mathbb{R}`, `\mathbb{C}`
- Functions: `f: A \to B`
- Logic: `\forall`, `\exists`, `\implies`, `\iff`
- Set operations: `\cup`, `\cap`, `\subseteq`, `\in`, `\notin`

## Content Structure Guidelines

### Definitions

Structure definition pages as follows:

1. **Formal Definition**: Start with the precise mathematical definition
2. **Intuitive Explanation**: Provide an accessible explanation
3. **Key Properties**: List important properties (if any)
4. **Related Concepts**: Link to related definitions using `@` syntax
5. **Examples**: Link to example pages using `@` syntax

### Theorems

Structure theorem pages as follows:

1. **Statement**: Clear statement of the theorem
2. **Prerequisites**: List all required definitions/theorems using `@` syntax
3. **Proof**: Complete proof (or proof sketch for complex theorems)
4. **Significance**: Explain why the theorem is important
5. **Applications**: Link to theorems that use this result

### Examples

Structure example pages as follows:

1. **Context**: State what concept this exemplifies using `@` syntax
2. **Construction**: Describe the example clearly
3. **Verification**: Show why it satisfies the definition
4. **Properties**: Highlight interesting properties
5. **Counterexample**: If applicable, show what it doesn't satisfy

## Writing Style

### Language Guidelines

- Use clear, precise mathematical language
- Define all notation before using it
- Write in present tense for mathematical facts
- Use active voice when possible
- Avoid unnecessarily complex sentences

### Accessibility

- Provide intuitive explanations alongside formal definitions
- Use examples to illustrate abstract concepts
- Break complex proofs into clear steps
- Highlight key insights and intuitions

## Quality Checklist

Before marking content as `status: "complete"`, ensure:

- [ ] All YAML front matter fields are correctly filled
- [ ] All references use `@` syntax
- [ ] Mathematical notation is properly formatted in LaTeX
- [ ] The content is mathematically correct
- [ ] All prerequisites are explicitly linked
- [ ] At least one example is provided (for definitions)
- [ ] The explanation is clear and accessible
- [ ] File naming convention is followed
- [ ] File is in the correct directory

## Common Pitfalls to Avoid

1. **Missing Cross-References**: Forgetting to use `@` syntax for concept mentions
2. **Incorrect IDs**: Mismatch between `id` field and cross-reference labels
3. **Circular Dependencies**: A depends on B, B depends on A
4. **Orphaned Content**: Pages with no incoming or outgoing links
5. **Inconsistent Notation**: Using different symbols for the same concept
6. **Missing Prerequisites**: Not listing all required concepts in proofs

## Advanced Features

### Custom Metadata

You can add custom fields to the YAML front matter for specific needs:

```yaml
computational_complexity: "O(n log n)"
first_proved_by: "Carl Friedrich Gauss"
year_discovered: 1801
```

### Multiple Examples

When a concept has multiple examples, create separate example files and link them:

```markdown
Common examples include:
- @ex-integers-addition
- @ex-matrices-multiplication
- @ex-polynomial-ring
```

### Proof Variations

For theorems with multiple proofs, you can note this:

```yaml
proof_methods: ["direct", "contradiction", "induction"]
```

## Maintenance Guidelines

### Status Progression

Content typically progresses through these stages:
1. `stub`: Minimal content, may be incomplete
2. `draft`: Complete content, needs review
3. `complete`: Reviewed and verified
4. `verified`: Formally verified (e.g., in Lean)

### Regular Reviews

- Check for broken cross-references monthly
- Update content when new related theorems are added
- Verify mathematical correctness during reviews
- Keep examples current and relevant

## Getting Help

If you have questions about the style guide or encounter situations not covered here:

1. Check existing content for examples
2. Consult the project documentation
3. Ask in the project discussion forum
4. Submit a style guide clarification request

Remember: Consistency is key to building a high-quality, interconnected mathematical knowledge base.
