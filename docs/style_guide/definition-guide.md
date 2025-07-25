# Definition Authoring Guidelines

## What Makes a Good Definition Page

Definitions are the building blocks of mathematical knowledge. A well-written definition page should:

1. **Be mathematically precise** while remaining accessible
2. **Link to all prerequisite concepts** using cross-references
3. **Provide clear notation** and explain symbols used
4. **Include multiple examples** to illustrate the concept
5. **Connect to related definitions** in the knowledge graph

## Content Structure

Structure definition pages as follows:

1. **Formal Definition**: Start with the precise mathematical definition
2. **Intuitive Explanation**: Provide an accessible explanation
3. **Key Properties**: List important properties (if any)
4. **Related Concepts**: Link to related definitions using `@` syntax
5. **Examples**: Link to example pages using `@` syntax

## Definition File Template

```yaml
---
title: "Definition: [Concept Name]"
id: "def-[concept-name]"
type: "Definition"
status: "complete"
requires:
  - "def-prerequisite1"
  - "def-prerequisite2"
lean_id: "Mathlib.Category.Module"  # Optional: Lean formalization
---

# Definition: [Concept Name] {#def-[concept-name]}

A **[concept]** is a [@prerequisite1](path/to/prerequisite1.qmd) that satisfies the following [conditions/properties]:

## Formal Definition

[Precise mathematical statement. For structures, list all axioms/properties]

1. **Property 1**: For all $x, y \in X$,
   $$[mathematical expression]$$

2. **Property 2**: There exists $e \in X$ such that
   $$[mathematical expression]$$

3. **Property 3**: [Additional properties as needed]

## Notation

- Standard notation: $[symbol]$ or $[notation]$
- Alternative notations: [if any]
- Conventions: [e.g., "We write $xy$ instead of $x \cdot y$"]

## Intuitive Understanding

[Accessible explanation that helps readers grasp the concept. Use analogies, visual descriptions, or informal language to build intuition.]

## Key Properties

[Important properties that follow immediately from the definition:]

- **Property name**: [Statement]
- **Uniqueness**: [If applicable]
- **Existence**: [If applicable]

## Examples

Common examples include:
- @ex-[example1]: [Brief description]
- @ex-[example2]: [Brief description]
- @ex-[example3]: [Brief description]

## Special Types

[If applicable, list important special cases:]

- **[Special type 1]**: A [concept] that also satisfies [additional property]
- **[Special type 2]**: When [specific condition holds]

See:
- @def-[special-type1]
- @def-[special-type2]

## Related Concepts

- **Generalizations**: @def-[more-general-concept]
- **Specializations**: @def-[more-specific-concept]
- **Similar structures**: @def-[analogous-concept]
```

## Best Practices for Definition Pages

### 1. Prerequisites and Dependencies

- **List all prerequisites** in the `requires` field
- **Link to prerequisites** in the definition text using `@` syntax
- **Order matters**: List prerequisites from most fundamental to most specific
- **Avoid circular dependencies**: Check that prerequisites don't depend on this definition

### 2. Mathematical Precision

- **Use standard notation** from the field
- **Define all symbols** before using them
- **Be explicit about quantifiers** (∀, ∃)
- **Specify domains** clearly (e.g., "for all $x \in \mathbb{R}$")

### 3. Examples and Non-Examples

- **Create separate example files** for each major example
- **Link to counterexamples** when instructive
- **Show edge cases** that test the definition boundaries
- **Include both abstract and concrete examples**

### 4. Notation Guidelines

- **Introduce notation clearly**: "We denote this as..."
- **Explain operator precedence**: When ambiguity might arise
- **Note common variations**: Different books/fields may use different notation
- **Be consistent**: Use the same notation throughout the project

### 5. Cross-References

- **Always use `@` syntax** for mathematical concepts
- **Link on first mention** in each major section
- **Don't over-link**: Once per section is usually enough
- **Check link validity**: Ensure target files exist

## Common Pitfalls to Avoid

1. **Incomplete Prerequisites**: Missing essential concepts in `requires`
2. **Circular Definitions**: Defining A in terms of B, and B in terms of A
3. **Ambiguous Notation**: Using symbols without clear definition
4. **No Examples**: Definitions without concrete instances
5. **Overly Technical**: No intuitive explanation provided
6. **Inconsistent Terminology**: Using different terms for the same concept
7. **Missing Edge Cases**: Not clarifying boundary conditions

## Writing Style Guidelines

### Language and Tone

- **Start with "A [concept] is..."** for consistency
- **Use active voice** when possible
- **Bold the concept** on first definition
- **Present tense** for mathematical facts
- **Avoid unnecessary jargon**

### Structure and Flow

1. **Definition first**: State what it is before discussing properties
2. **Simple to complex**: Build up from basic ideas
3. **General to specific**: Present the general case before special cases
4. **Concrete examples**: Follow abstract definitions with examples

### Mathematical Formatting

- **Display important equations** using `$$...$$`
- **Inline math** for simple expressions: `$...$`
- **Number equations** when referenced later
- **Align multi-line equations** for readability

## Domain-Specific Considerations

### Algebra

- State whether operations are commutative
- Clarify when discussing left vs. right operations
- Include finite vs. infinite cases

### Analysis

- Be explicit about metric/norm being used
- State completeness assumptions
- Clarify pointwise vs. uniform properties

### Topology

- Specify whether spaces are Hausdorff, compact, etc.
- Be clear about open vs. closed sets
- Note separation axioms satisfied

### Category Theory

- Draw or describe commutative diagrams
- Specify variance (covariant/contravariant)
- State size issues when relevant

## File Organization

- **File name**: `def-[concept-name].qmd`
- **Location**: Place in the primary domain directory
- **Cross-domain concepts**: Choose the most fundamental domain
- **Naming conventions**: Use lowercase with hyphens

## Metadata Guidelines

### Required Fields

```yaml
title: "Definition: [Name]" # Exact format required
id: "def-[concept]" # Must match filename
type: "Definition" # Case-sensitive
status: "complete" # Or: stub, draft, verified
requires: ["def-1", "def-2"] # List all prerequisites
```

### Optional Fields

```yaml
lean_id: "Mathlib.Module.Path" # Lean formalization
author: "Your Name" # Content author
date_created: "2025-01-25" # ISO format
related_concepts: ["def-x"] # Additional relationships
domain_specific: true # Domain-specific variant
```

## Quality Checklist

Before marking a definition as `complete`:

- [ ] All prerequisites listed in `requires`
- [ ] All mathematical symbols defined
- [ ] At least 2-3 examples provided or linked
- [ ] Intuitive explanation included
- [ ] Cross-references use `@` syntax
- [ ] Notation section if special symbols used
- [ ] Related concepts linked
- [ ] No circular dependencies
- [ ] Consistent with domain conventions
- [ ] Examples cover typical and edge cases

## Examples of Well-Written Definitions

Study these for reference:

- @def-group: Clear axioms, good examples, notation explained
- @def-topology: Complex concept made accessible
- @def-continuous-function: Multiple equivalent formulations
