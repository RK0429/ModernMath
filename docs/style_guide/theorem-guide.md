# Theorem Authoring Guidelines

## What Makes a Good Theorem Page

Theorems are the core results of mathematics. A well-written theorem page should:

1. **State the theorem precisely** with clear hypotheses and conclusions
2. **List all prerequisites** needed to understand the statement and proof
3. **Provide complete or sketched proofs** depending on complexity
4. **Explain significance** and why the result matters
5. **Link to applications** and related results

## Content Structure

Structure theorem pages as follows:

1. **Statement**: Clear statement of the theorem
2. **Prerequisites**: List all required definitions/theorems using `@` syntax
3. **Proof**: Complete proof (or proof sketch for complex theorems)
4. **Significance**: Explain why the theorem is important
5. **Applications**: Link to theorems that use this result

## Theorem File Template

```yaml
---
title: "Theorem: [Theorem Name]"
id: "thm-[theorem-name]"
type: "Theorem"
status: "complete"
requires:
  - "def-concept1"
  - "def-concept2"
  - "thm-prerequisite"
lean_id: "Mathlib.Category.Theorem"  # Optional
---

# [Theorem Name] {#thm-[theorem-name]}

[One-paragraph overview stating what the theorem says and why it's important]

## Statement

Let [setup/hypotheses]. Then [conclusion].

**Formal Statement**: [If the informal statement above needs clarification]

### Alternative Formulations

[If applicable, other equivalent ways to state the theorem]

## Prerequisites

This theorem requires understanding of:
- @def-[concept1]: [Why needed]
- @def-[concept2]: [Why needed]
- @thm-[prerequisite]: [If the proof uses other theorems]

## Proof

[Choose one of the following approaches:]

### Option 1: Complete Proof
[Step-by-step proof with clear reasoning]

### Option 2: Proof Sketch
[For complex proofs, provide key ideas and steps]

**Key Ideas**:
1. [Main insight 1]
2. [Main insight 2]

**Proof Structure**:
1. [Step 1 overview]
2. [Step 2 overview]
3. [Final step]

### Option 3: Multiple Proofs
[If the theorem has notably different proofs]

#### Proof 1: [Method Name]
[First proof approach]

#### Proof 2: [Alternative Method]
[Second proof approach]

## Significance

[Why this theorem matters:]
- **Theoretical importance**: [Impact on the field]
- **Practical applications**: [Real-world uses]
- **Historical context**: [Development and influence]

## Corollaries

Direct consequences of this theorem:

1. **Corollary 1**: [Statement]
2. **Corollary 2**: [Statement]

See also:
- @cor-[corollary1]
- @cor-[corollary2]

## Applications

This theorem is used in:
- @thm-[theorem1]: [How it's used]
- @thm-[theorem2]: [How it's used]
- [Area of mathematics]: [General application]

## Examples

- @ex-[example1]: [Illustrates aspect 1]
- @ex-[example2]: [Illustrates aspect 2]

## Related Results

- **Generalizations**: @thm-[more-general]
- **Special cases**: @thm-[special-case]
- **Converse**: @thm-[converse] (if exists)
```

## Types of Theorems

### Classification by Type

- **Theorem**: Major results with significant impact
- **Proposition**: Important results, but less central than theorems
- **Lemma**: Technical results used primarily in other proofs
- **Corollary**: Direct consequences of theorems
- **Criterion**: Characterization giving necessary and sufficient conditions

### File Naming Conventions

- Theorems: `thm-[name].qmd`
- Propositions: `prop-[name].qmd`
- Lemmas: `lem-[name].qmd`
- Corollaries: `cor-[name].qmd`

## Proof Writing Guidelines

### Structure and Clarity

1. **Start with proof strategy**: "We will prove this by..."
2. **Define notation**: Introduce any proof-specific symbols
3. **Break into cases**: When applicable, clearly delineate cases
4. **Signal key steps**: "The key observation is..."
5. **End clearly**: Use □, QED, or "This completes the proof"

### Common Proof Techniques

- **Direct Proof**: State assumptions, derive conclusion
- **Contradiction**: Assume negation, derive contradiction
- **Induction**: Base case, inductive step (link to @ax-induction)
- **Construction**: Build explicit examples
- **Contrapositive**: Prove ¬Q → ¬P instead of P → Q

### Proof Sketch Guidelines

For complex proofs, provide:

1. **Main idea**: One-paragraph intuition
2. **Key lemmas**: Technical results needed
3. **Proof outline**: Major steps without full details
4. **References**: Where to find complete proof

### What to Include/Exclude

**Include**:

- All non-trivial steps
- Justification for each claim
- References to used results
- Intuition for key insights

**Exclude**:

- Routine calculations (unless instructive)
- Standard technical details
- Overly formal notation (unless necessary)

## Best Practices

### 1. Prerequisites Management

- **Minimal prerequisites**: List only what's essential
- **Explain usage**: Note why each prerequisite is needed
- **Order logically**: From most basic to most advanced
- **Distinguish types**: Separate "to understand" vs "for proof"

### 2. Statement Clarity

- **Precise hypotheses**: State all assumptions explicitly
- **Clear conclusion**: Unambiguous statement of result
- **Quantifiers**: Be explicit about ∀ and ∃
- **Edge cases**: Address or explicitly exclude

### 3. Historical and Contextual Notes

- **Attribution**: Credit original discoverers
- **Development**: How the theorem evolved
- **Motivation**: Why it was originally proved
- **Impact**: How it changed the field

### 4. Computational Aspects

- **Algorithms**: If theorem leads to algorithms
- **Complexity**: Computational complexity when relevant
- **Constructive**: Note if proof is constructive
- **Examples**: Computational examples when helpful

## Common Pitfalls to Avoid

1. **Incomplete hypotheses**: Missing necessary conditions
2. **Circular reasoning**: Using what you're trying to prove
3. **Handwaving**: "It's obvious that..." without justification
4. **Missing cases**: Incomplete case analysis
5. **Unclear notation**: Using symbols without definition
6. **No motivation**: Stating result without context
7. **No examples**: Abstract theorem without concrete instances

## Domain-Specific Guidelines

### Analysis

- State domains and codomains precisely
- Specify which topology/metric
- Be clear about pointwise vs uniform
- Note completeness assumptions

### Algebra

- Specify finite vs infinite
- Note commutativity assumptions
- Be clear about left vs right operations
- State characteristic assumptions

### Topology

- Specify separation axioms
- Note compactness/connectedness
- Be clear about subspace topology
- State covering assumptions

### Number Theory

- Specify integer vs rational vs real
- Note prime/coprimality assumptions
- Be clear about divisibility
- State congruence relations

## Quality Checklist

Before marking complete:

- [ ] Statement is mathematically precise
- [ ] All hypotheses explicitly stated
- [ ] Prerequisites listed and linked
- [ ] Proof is complete or clearly sketched
- [ ] Significance explained
- [ ] Applications/corollaries noted
- [ ] Examples provided or linked
- [ ] Cross-references use @ syntax
- [ ] No circular dependencies
- [ ] Notation clearly defined

## Metadata Requirements

### Required Fields

```yaml
title: "Theorem: [Name]" # Or Proposition:/Lemma:/Corollary:
id: "thm-[name]" # Match type: prop-, lem-, cor-
type: "Theorem" # Or Proposition, Lemma, Corollary
status: "complete" # Or stub, draft, verified
requires: ["def-1", "thm-2"] # All prerequisites
```

### Optional Fields

```yaml
lean_id: "Mathlib.Path" # Lean formalization
first_proved: "1801" # Year of first proof
proved_by: "Gauss" # Original discoverer
proof_technique: "induction" # Primary method
importance: "fundamental" # fundamental/major/technical
computational: true # If algorithmically relevant
```

## Examples of Well-Written Theorems

Study these for reference:

- @thm-lagrange: Clear statement, important corollaries
- @thm-fundamental-algebra: Multiple proofs presented
- @thm-inverse-function: Precise technical conditions
