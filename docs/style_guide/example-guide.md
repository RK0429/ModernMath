# Example Authoring Guidelines

## What Makes a Good Example Page

Examples bring abstract mathematical concepts to life. A well-written example page should:

1. **Clearly state what concept it exemplifies** using cross-references
2. **Provide complete construction** of the example
3. **Verify all required properties** systematically
4. **Highlight interesting features** that illustrate the concept
5. **Note what properties it doesn't have** (when instructive)

## Content Structure

Structure example pages as follows:

1. **Context**: State what concept this exemplifies using `@` syntax
2. **Construction**: Describe the example clearly
3. **Verification**: Show why it satisfies the definition
4. **Properties**: Highlight interesting properties
5. **Counterexample**: If applicable, show what it doesn't satisfy

## Example File Template

```yaml
---
title: "Example: [Example Name]"
id: "ex-[example-name]"
type: "Example"
status: "complete"
requires:
  - "def-concept-being-exemplified"
  - "def-prerequisite1"
  - "def-prerequisite2"
---

# Example: [Example Name] {#ex-[example-name]}

[Opening paragraph: State what this is an example of and give a brief overview]

The [object/structure] [brief description] is an example of a @def-[concept].

## Construction

[Detailed description of the example. Be explicit about:]
- The underlying set/space
- The operations/structure
- Any special notation

## Verification of [Concept] Properties

We verify that [example] satisfies all requirements of a @def-[concept]:

### 1. [Property 1 Name]

[Show this property holds]
- [Step-by-step verification]
- [Calculations if needed]

### 2. [Property 2 Name]

[Show this property holds]

### 3. [Additional Properties]

[Continue for all required properties]

## Additional Properties

Beyond being a [concept], this example also:

1. **Is a [special type]**: [Explanation]
2. **Has property X**: [Details]
3. **Satisfies condition Y**: [Verification]

## What This Example Is NOT

[When instructive, explain what properties it lacks:]

This example is not:
- A @def-[other-concept] because [specific failing property]
- [Another property] since [counterexample within the example]

## Computational Aspects

[If applicable:]
- **Explicit calculations**: [Show concrete computations]
- **Algorithms**: [How to compute with this example]
- **Complexity**: [Computational complexity if relevant]

## Variations

Related examples that modify this construction:
- @ex-[variant1]: [How it differs]
- @ex-[variant2]: [How it differs]

## Significance

This example is important because:
- **Canonical example**: [If it's the standard example]
- **Counterexample**: [If it disproves something]
- **Boundary case**: [If it shows edge behavior]
- **Motivation**: [If it motivated the definition]
```

## Types of Examples

### By Purpose

1. **Canonical Examples**: The standard, go-to examples
2. **Counterexamples**: Show what can go wrong
3. **Edge Cases**: Boundary behavior
4. **Non-Examples**: Explicitly fail some property
5. **Pathological Examples**: Unusual but instructive cases

### By Complexity

1. **Simple/Concrete**: Easy to understand (e.g., finite sets)
2. **Standard**: Typical examples from the field
3. **Advanced**: Require deeper knowledge
4. **Pathological**: Counterintuitive but valid

## Best Practices

### 1. Verification Completeness

- **Check every property**: Don't skip "obvious" ones
- **Be explicit**: Show calculations and reasoning
- **Order logically**: Start with most basic properties
- **Reference definitions**: Link to property being verified

### 2. Clarity and Accessibility

- **Start simple**: Begin with intuitive description
- **Build complexity**: Add technical details gradually
- **Use visuals**: Diagrams, tables, or graphs when helpful
- **Concrete numbers**: Use specific values in calculations

### 3. Educational Value

- **Highlight key insights**: What makes this example tick?
- **Compare and contrast**: Relate to other examples
- **Show limitations**: What it doesn't illustrate
- **Computational examples**: Include calculations

### 4. Non-Example Sections

When showing what something is NOT:

- **Be specific**: Name the exact failing property
- **Give counterexample**: Show specific failure
- **Explain why**: Help build intuition
- **Link to examples**: That DO have the property

## Common Pitfalls to Avoid

1. **Incomplete verification**: Skipping property checks
2. **Assuming knowledge**: Using concepts not in prerequisites
3. **No concrete values**: Too abstract for an example
4. **Missing the point**: Not highlighting what makes it interesting
5. **Poor organization**: Jumping between properties
6. **Circular reasoning**: Using what you're exemplifying
7. **Too complex**: Starting with pathological cases

## Writing Guidelines

### Structure and Flow

1. **State purpose immediately**: "X is an example of Y"
2. **Define before using**: Introduce all notation
3. **Systematic verification**: Check properties in order
4. **Build intuition**: Explain why properties hold
5. **Summarize significance**: Why this example matters

### Mathematical Precision

- **Define the object completely**: All components explicit
- **State domains clearly**: Where elements come from
- **Show all work**: Include calculations
- **Justify claims**: Even "obvious" ones

### Pedagogical Considerations

- **Multiple representations**: Algebraic, geometric, etc.
- **Increasing complexity**: Start simple, add nuance
- **Common mistakes**: Address likely confusions
- **Connections**: Relate to other examples

## Domain-Specific Guidelines

### Algebra

- Show closure explicitly
- Verify all axioms systematically
- Include multiplication/addition tables for finite examples
- Note whether commutative, associative, etc.

### Analysis

- Be explicit about metric/norm
- Show limit calculations
- Verify continuity/differentiability at points
- Include epsilon-delta arguments when needed

### Topology

- Draw diagrams when possible
- List open sets explicitly (for finite examples)
- Verify axioms: unions, intersections, empty, whole space
- Show specific open neighborhoods

### Category Theory

- Define objects and morphisms explicitly
- Verify composition and identity
- Draw commutative diagrams
- Show specific functor actions

### Number Theory

- Use concrete numbers
- Show divisibility explicitly
- Include modular arithmetic calculations
- Verify prime factorizations

## Quality Checklist

Before marking complete:

- [ ] States what it exemplifies clearly
- [ ] All prerequisities listed
- [ ] Construction fully described
- [ ] Every property verified
- [ ] Calculations shown explicitly
- [ ] Interesting features highlighted
- [ ] Non-properties noted (if relevant)
- [ ] Cross-references use @ syntax
- [ ] Concrete values used
- [ ] Educational value clear

## File Organization

- **File name**: `ex-[descriptive-name].qmd`
- **Location**: Same directory as concept being exemplified
- **Multiple examples**: Use descriptive suffixes
- **Naming**: Be specific (e.g., `ex-integers-addition` not `ex-group1`)

## Metadata Guidelines

### Required Fields

```yaml
title: "Example: [Descriptive Name]"
id: "ex-[name]" # Must match filename
type: "Example" # Exactly this
status: "complete" # Or stub, draft, verified
requires: ["def-1", "def-2"] # What's being exemplified + prerequisites
```

### Optional Fields

```yaml
lean_id: "Mathlib.Examples.Path" # If formalized
counterexample_to: "thm-x" # If disproving something
canonical: true # If THE standard example
pathological: true # If counterintuitive
computational_example: true # If focuses on computation
```

## Examples of Well-Written Examples

Study these for reference:

- @ex-integers-addition: Clear verification of all group axioms
- @ex-real-line-metric: Shows metric space properties systematically
- @ex-finite-field: Includes explicit multiplication tables

## Special Types of Examples

### Canonical Examples

These deserve extra care as they're referenced frequently:

- Include multiple viewpoints
- Show all basic properties
- Link to generalizations
- Explain historical importance

### Counterexamples

When disproving statements:

- State clearly what's being disproven
- Show the specific failure point
- Explain why other properties still hold
- Note minimal modifications that would work

### Pathological Examples

For counterintuitive cases:

- Build up gradually
- Explain why it's surprising
- Show it satisfies the definition
- Discuss what intuition it breaks

### Computational Examples

When computation is key:

- Show step-by-step calculations
- Include multiple instances
- Explain the algorithm
- Give complexity analysis
