# Math Environments Extension

This Quarto extension provides custom mathematical environments for theorems, definitions, lemmas, propositions, corollaries, examples, and proofs.

## Installation

This extension is already installed in the `_extensions/math-environments/` directory.

## Usage

### Basic Syntax

Use div syntax with the appropriate class:

```markdown
::: {.theorem #thm-label title="Optional Title"}
Content of the theorem goes here.
:::

::: {.definition #def-label}
Content of the definition goes here.
:::

::: {.proof}
Content of the proof goes here.
:::
```

### Available Environments

1. **Theorem**: `.theorem`
2. **Definition**: `.definition`
3. **Lemma**: `.lemma`
4. **Proposition**: `.proposition`
5. **Corollary**: `.corollary`
6. **Example**: `.example`
7. **Proof**: `.proof`

### Features

- **Automatic numbering**: Theorems, definitions, etc. are automatically numbered
- **Cross-references**: Use labels with `#label` syntax and reference with `@label`
- **Optional titles**: Add `title="Your Title"` attribute
- **Consistent styling**: Different colors and styles for each environment type
- **Dark mode support**: Automatically adjusts colors for dark themes
- **PDF support**: Beautiful LaTeX formatting for PDF output

### Examples

#### Theorem with Title
```markdown
::: {.theorem #thm-fundamental title="Fundamental Theorem of Algebra"}
Every non-constant polynomial with complex coefficients has at least one complex root.
:::
```

#### Definition
```markdown
::: {.definition #def-group}
A **group** is a set $G$ together with a binary operation $\cdot: G \times G \to G$ 
satisfying:

1. **Associativity**: $(a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. **Identity**: There exists $e \in G$ such that $e \cdot a = a \cdot e = a$
3. **Inverse**: For each $a \in G$, there exists $a^{-1} \in G$ such that 
   $a \cdot a^{-1} = a^{-1} \cdot a = e$
:::
```

#### Proof
```markdown
::: {.proof}
We proceed by induction on $n$.

**Base case**: For $n = 1$, the statement is trivially true.

**Inductive step**: Assume the statement holds for $n = k$. 
We need to show it holds for $n = k + 1$.
[... proof continues ...]

Therefore, by mathematical induction, the statement holds for all $n \in \mathbb{N}$.
:::
```

### Cross-referencing

Reference environments using the `@` syntax:

```markdown
As shown in @thm-fundamental, every polynomial has a root.

By @def-group, we know that groups have an identity element.
```

### Customization

The appearance can be customized by modifying:
- `math-environments.css` for HTML output
- `math-environments.tex` for PDF output

## Technical Details

- The Lua filter processes div blocks with specific classes
- Counters are maintained for automatic numbering
- The proof environment automatically adds a QED symbol (□)
- Labels are converted to proper anchors for cross-referencing