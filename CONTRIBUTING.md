# Contributing to the Mathematics Knowledge Graph Wiki

Thank you for your interest in contributing to the Mathematics Knowledge Graph Wiki! This guide will help you understand how to contribute effectively to this project.

## Table of Contents

- [Getting Started](#getting-started)
- [Types of Contributions](#types-of-contributions)
- [Development Setup](#development-setup)
- [Content Guidelines](#content-guidelines)
- [Code Contribution Process](#code-contribution-process)
- [Style Guidelines](#style-guidelines)
- [Testing](#testing)
- [Submitting Changes](#submitting-changes)

## Getting Started

Before contributing, please:

1. Read the [README.md](README.md) to understand the project
2. Check existing [issues](https://github.com/RK0429/ModernMath/issues) to avoid duplicate work
3. Review the [style guide](docs/style-guide.md) for content formatting

## Types of Contributions

### 1. Mathematical Content

- **New Concepts**: Add definitions, theorems, axioms, or examples
- **Improvements**: Enhance existing explanations or add clarifications
- **Corrections**: Fix mathematical errors or typos
- **Cross-References**: Add links between related concepts

### 2. Code Contributions

- **Scripts**: Improve graph extraction or visualization scripts
- **API Enhancements**: Add new endpoints or improve existing ones
- **Bug Fixes**: Fix issues in the processing pipeline
- **Documentation**: Improve code documentation

### 3. Formal Verification

- **Lean Proofs**: Add formal proofs for theorems
- **Verification Mappings**: Link informal content to formal proofs

## Development Setup

### Prerequisites

- Python 3.11+
- Poetry for dependency management
- Quarto 1.4+ for content rendering
- Git for version control
- (Optional) Lean 4 for formal verification
- (Optional) Java 11+ for SPARQL endpoint

### Installation

1. Clone the repository:
   ```bash
   git clone https://github.com/RK0429/ModernMath.git
   cd ModernMath
   ```

2. Install Python dependencies:
   ```bash
   poetry install
   ```

3. Activate the virtual environment:
   ```bash
   poetry shell
   ```

## Content Guidelines

### File Structure

Content is organized by mathematical domain:

```
content/
├── algebra/
├── analysis/
├── topology/
├── geometry/
├── number-theory/
├── combinatorics/
├── logic-set-theory/
├── probability-statistics/
└── category-theory/
```

### File Naming Convention

- Definitions: `def-<concept-name>.qmd`
- Theorems: `thm-<theorem-name>.qmd`
- Examples: `ex-<example-name>.qmd`
- Axioms: `ax-<axiom-name>.qmd`

### Required Metadata

Every `.qmd` file must include YAML front matter:

```yaml
---
title: "Definition: Group"
id: "def-group"
type: "Definition"
status: "complete"  # stub, draft, complete, or verified
domain: "Algebra"   # Inherited from _metadata.yml
requires:
  - "def-set"
  - "def-binary-operation"
---
```

### Cross-References

Always use Quarto's cross-reference syntax:

```markdown
A group is a @def-set equipped with a @def-binary-operation...
```

### Mathematical Notation

Use LaTeX for all mathematical expressions:

```markdown
Inline math: $G$ is a group if $(G, \cdot)$ satisfies...

Display math:
$$
\forall a, b, c \in G: (a \cdot b) \cdot c = a \cdot (b \cdot c)
$$
```

## Code Contribution Process

### 1. Python Scripts

- Follow PEP 8 style guidelines
- Add type hints for all functions
- Include docstrings for modules, classes, and functions
- Maximum line length: 100 characters

Example:

```python
def extract_cross_references(content: str) -> List[str]:
    """Extract all @label cross-references from Markdown content.

    Args:
        content: The Markdown content to parse

    Returns:
        List of cross-reference labels found
    """
    pattern = re.compile(r'@([a-zA-Z0-9_-]+)')
    return pattern.findall(content)
```

### 2. Running Code Quality Checks

Before submitting:

```bash
# Format code
poetry run black scripts/

# Check linting
poetry run flake8 scripts/ --max-line-length=100

# Type checking
poetry run mypy scripts/
```

## Testing

### Content Validation

Validate metadata before building:

```bash
poetry run python scripts/validation/validate_metadata.py
```

### Graph Validation

After making changes to content:

```bash
# Rebuild the knowledge graph
poetry run python scripts/graph/build_graph.py

# Validate the graph structure
poetry run python scripts/graph/validate_graph.py
```

### API Testing

If modifying the API:

```bash
# Run API tests
poetry run pytest api/test_api.py
```

## Submitting Changes

### 1. Create a Branch

```bash
git checkout -b feature/your-feature-name
```

### 2. Make Your Changes

- Keep commits focused and atomic
- Write clear commit messages
- Reference issues when applicable

### 3. Build and Test

```bash
# Build the knowledge graph
poetry run python scripts/graph/build_graph.py

# Generate visualizations
poetry run python scripts/visualization/generate_pyvis.py

# Preview the site
quarto preview
```

### 4. Submit a Pull Request

1. Push your branch to GitHub
2. Create a pull request with:
   - Clear title describing the change
   - Detailed description of what and why
   - Reference to any related issues
   - Screenshots for visual changes

### 5. PR Review Process

- All PRs require at least one review
- Address reviewer feedback promptly
- Ensure CI checks pass
- Maintain a clean commit history

## Style Guidelines

### Commit Messages

Follow conventional commits format:

```
type(scope): subject

body (optional)

footer (optional)
```

Types:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `style`: Code style changes
- `refactor`: Code refactoring
- `test`: Test additions/changes
- `chore`: Build process or auxiliary tool changes

Example:
```
feat(algebra): add definition of normal subgroup

- Added def-normal-subgroup.qmd
- Updated group theory index
- Added cross-references from def-subgroup

Closes #42
```

### Documentation

- Use clear, concise language
- Provide examples where helpful
- Keep technical jargon to a minimum
- Update relevant documentation when changing functionality

## Questions?

If you have questions:

1. Check existing [documentation](docs/)
2. Search [issues](https://github.com/RK0429/ModernMath/issues)
3. Open a new issue for discussion

Thank you for contributing to the Mathematics Knowledge Graph Wiki!
