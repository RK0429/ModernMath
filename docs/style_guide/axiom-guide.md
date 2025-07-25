# Axiom Authoring Guidelines

## What Makes a Good Axiom Page

Axioms are foundational assumptions in mathematics. Unlike theorems which are proven, axioms are accepted as true and form the basis for mathematical reasoning. A well-written axiom page should:

1. **State the axiom precisely** in both natural language and formal notation
2. **Provide intuitive understanding** of why this assumption is reasonable
3. **Explain its role** in the mathematical framework
4. **Link to consequences** that follow from this axiom
5. **Note relationships** to other axioms in the system

## Content Structure

Structure axiom pages as follows:

1. **Statement**: Clear, formal statement of the axiom
2. **Formal Statement**: Mathematical formulation using precise notation
3. **Variants**: Alternative formulations or equivalent statements (if applicable)
4. **Intuition**: Accessible explanation of what the axiom means
5. **Role in Mathematics**: Why this axiom is fundamental and what it enables
6. **Consequences**: Link to theorems and definitions that depend on this axiom
7. **Independence**: Note if the axiom is independent of others in the system (when relevant)

## Common Mathematical Axioms to Document

### Set Theory Axioms (ZFC)

- `ax-extensionality`: Two sets are equal if they have the same elements
- `ax-pairing`: For any two sets, there exists a set containing exactly those two sets
- `ax-union`: For any set of sets, there exists a set containing all their elements
- `ax-power-set`: For any set, there exists a set of all its subsets
- `ax-infinity`: There exists an infinite set
- `ax-separation`: Subsets defined by properties exist
- `ax-replacement`: Images of sets under functions exist
- `ax-regularity`: No set contains itself (no infinite descending chains)
- `ax-choice`: Every collection of non-empty sets has a choice function

### Number System Axioms

- `ax-induction`: Mathematical induction for natural numbers (already exists)
- `ax-peano-successor`: Every natural number has a successor
- `ax-peano-zero`: Zero is not the successor of any natural number
- `ax-field`: Field axioms for real numbers
- `ax-completeness`: Every bounded set of reals has a least upper bound
- `ax-archimedean`: No infinitesimals in the reals

### Geometric Axioms

- `ax-euclid-parallel`: Euclid's parallel postulate
- `ax-incidence`: Points and lines incidence properties
- `ax-betweenness`: Order properties of points on a line
- `ax-congruence`: Congruence of segments and angles

### Logic Axioms

- `ax-excluded-middle`: Every proposition is either true or false
- `ax-non-contradiction`: No proposition is both true and false
- `ax-identity`: Everything is identical to itself
- `ax-modus-ponens`: From P and P→Q, deduce Q

## Axiom File Template

```yaml
---
title: "Axiom: [Name]"
id: "ax-[short-name]"
type: "Axiom"
status: "complete"
requires: []  # Axioms typically have no prerequisites
---

# Axiom: [Full Name] {#ax-[short-name]}

[One-paragraph overview of the axiom and its significance]

## Statement

[Clear natural language statement of the axiom]

## Formal Statement

$$[Precise mathematical formulation]$$

## Variants

[Alternative formulations, if any. For example:]

### Equivalent Formulation

[Another way to state the same axiom]

### Weaker/Stronger Versions

[Related axioms that imply or are implied by this one]

## Intuition

[Accessible explanation with examples or analogies]

## Role in Mathematics

[Why this axiom is needed and what it enables]

### Consequences

Major results that depend on this axiom:
- @thm-[theorem1]
- @thm-[theorem2]

### Applications

Areas where this axiom is essential:
- [Mathematical field 1]
- [Mathematical field 2]

## Historical Context

[When and why this axiom was introduced, controversies if any]

## Independence

[If relevant, note whether this axiom is independent of others in the system]
```

## Best Practices for Axiom Pages

1. **Clarity Over Brevity**: Axioms are foundations - be thorough in explanation
2. **Multiple Perspectives**: Provide both formal and intuitive understanding
3. **Historical Context**: Include why the axiom was introduced when relevant
4. **Controversies**: Note any historical or philosophical debates (e.g., Axiom of Choice)
5. **Equivalent Forms**: Show different ways to state the same axiom
6. **Cross-System References**: Note how the axiom appears in different axiomatic systems

## Common Pitfalls to Avoid

1. **Circular Dependencies**: Axioms should not require other content
2. **Overly Technical**: Balance formal precision with accessibility
3. **Missing Consequences**: Always link to theorems that use the axiom
4. **Ignoring Alternatives**: Mention when alternative axioms exist (e.g., non-Euclidean geometries)
5. **Incomplete Formalization**: Provide complete formal statements, not just informal descriptions

## Axiom System Considerations

When adding axioms, consider:

1. **Minimality**: Is this axiom independent of others?
2. **Consistency**: Does it contradict existing axioms?
3. **Completeness**: What can/cannot be proven without it?
4. **Alternatives**: What happens if we replace it with something else?

## Examples of Well-Written Axiom Pages

See these examples for reference:

- @ax-induction: Clear statement with variants and intuitive explanation
- Future: @ax-choice, @ax-extensionality, @ax-completeness

## Special Notes for Common Axioms

### Axiom of Choice

- Mention its equivalence to Zorn's Lemma and Well-Ordering Theorem
- Note its controversial nature and constructivist alternatives
- List important consequences (e.g., Banach-Tarski paradox)

### Continuum Hypothesis

- Explain its independence from ZFC
- Discuss its implications for set theory
- Note Gödel and Cohen's contributions

### Parallel Postulate

- Compare Euclidean vs. non-Euclidean geometries
- Show alternative formulations (Playfair's axiom)
- Discuss historical attempts to prove it from other axioms

## File Naming and Organization

- **File name**: `ax-[concept-name].qmd` (e.g., `ax-choice.qmd`)
- **Location**: Place in the most relevant domain directory
- **Cross-domain axioms**: Place in `logic-set-theory/` by default
- **ID format**: Must match filename without extension

## Metadata Requirements

Required YAML fields:

```yaml
title: "Axiom: [Full Name]" # Format: "Axiom: " + name
id: "ax-[short-name]" # Must match filename
type: "Axiom" # Exactly this capitalization
status: "complete" # Usually complete for axioms
requires: [] # Usually empty for axioms
```

Optional fields:

```yaml
lean_id: "Mathlib.Logic.Basic" # If formalized in Lean
historical_name: "Fifth Postulate" # Alternative names
first_stated: "300 BCE" # Historical information
controversial: true # For debated axioms
```
