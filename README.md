# Mathematics Knowledge Graph Wiki

A semantic wiki for mathematics built as a knowledge graph using Quarto, RDF/OWL, and modern web technologies.

## Overview

This project creates an evolving, queryable wiki covering all fields of mathematics as a knowledge graph. It represents axioms, definitions, theorems, and examples as interconnected nodes, allowing users and machines to explore mathematical relationships and dependencies.

## Features

- 📚 **Structured Content**: Mathematical concepts organized as nodes with formal relationships
- 🔍 **SPARQL Queries**: Query the knowledge graph to find dependencies, examples, and connections
- 🌐 **Linked Data**: Published as RDF/OWL for semantic web compatibility
- 📊 **Interactive Visualizations**: Mermaid diagrams showing concept relationships
- 🤖 **Automated Validation**: CI/CD pipeline ensures content integrity
- 🔬 **Formal Verification Ready**: Designed for future Lean 4 integration

## Quick Start

### Prerequisites

- Python 3.11+
- Poetry (for dependency management)
- Quarto 1.4+ (for content rendering)
- Git

### Installation

1. **Clone the repository:**

   ```bash
   git clone https://github.com/yourusername/ModernMath.git
   cd ModernMath
   ```

2. **Install dependencies:**

   ```bash
   poetry install
   ```

3. **Build the knowledge graph:**

   ```bash
   poetry run python scripts/build_graph.py
   ```

4. **Generate visualizations:**

   ```bash
   poetry run python scripts/generate_mermaid.py
   poetry run python scripts/insert_diagrams.py
   ```

5. **Preview the site:**

   ```bash
   quarto preview
   ```

## Project Structure

```text
ModernMath/
├── content/              # Mathematical content organized by domain
│   ├── algebra/         # Algebra concepts
│   ├── topology/        # Topology concepts
│   └── ...              # Other mathematical domains
├── ontology/            # RDF/OWL ontology definitions
├── scripts/             # Python scripts for graph processing
├── fuseki/              # Apache Jena Fuseki SPARQL endpoint
├── output/              # Generated files (knowledge graph, etc.)
├── _quarto.yml          # Quarto configuration
└── pyproject.toml       # Python dependencies
```

## Usage

### Adding Content

1. Create a new `.qmd` file in the appropriate domain folder
2. Include required YAML metadata:

   ```yaml
   ---
   title: "Definition: Your Concept"
   id: "def-your-concept"
   type: "Definition"
   status: "draft"
   ---
   ```

3. Write content using Markdown and LaTeX
4. Link to other concepts using `@id` syntax

### Querying the Knowledge Graph

1. **Start Fuseki server:**

   ```bash
   cd fuseki/scripts
   ./start_fuseki.sh
   ```

2. **Load data:**

   ```bash
   ./load_data.sh
   ```

3. **Query via command line:**

   ```bash
   poetry run python scripts/query_graph.py find-type Definition
   ```

4. **Or use SPARQL directly:**
   - Web UI: <http://localhost:3030/>
   - Endpoint: <http://localhost:3030/mathwiki/sparql>

## Deployment

### GitHub Pages (Automatic)

The project automatically deploys to GitHub Pages when you push to the `main` branch.

1. Enable GitHub Pages in repository settings
2. Select `gh-pages` branch as source
3. Push changes to `main`
4. Access at: `https://[username].github.io/ModernMath/`

See [docs/github-pages-deployment.md](docs/github-pages-deployment.md) for detailed deployment instructions.

## Development

### Running Tests

```bash
poetry run pytest
```

### Code Quality

```bash
poetry run black scripts/
poetry run flake8 scripts/
poetry run mypy scripts/
```

### Building Documentation

```bash
quarto render
```

### Validation Tools

#### Local Cross-Reference Validation

Check for broken cross-references without full rendering:

```bash
# Quick check all files
./check-refs.sh

# Check specific file
poetry run python scripts/check_cross_references.py --file content/algebra/def-group.qmd

# Verbose output
poetry run python scripts/check_cross_references.py --verbose
```

#### Pre-commit Hooks

This project uses pre-commit hooks to ensure code quality:

```bash
# Install pre-commit hooks (one-time setup)
poetry run pre-commit install

# Run all hooks manually
poetry run pre-commit run --all-files

# Run specific hook
poetry run pre-commit run check-cross-references --all-files
```

The hooks include:
- Cross-reference validation
- YAML metadata validation
- Python code formatting (Black)
- Python linting (Flake8)
- Python type checking (MyPy)
- Trailing whitespace removal
- End-of-file fixing

#### CI/CD Integration

The GitHub Actions workflow automatically validates cross-references:

1. **Pre-build validation**: Runs before building the knowledge graph
2. **Early failure detection**: Stops the build if invalid references are found
3. **Clear error messages**: Shows exact file and line numbers of issues

## Contributing

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-theorem`)
3. Add your content following the style guide
4. Ensure all links are properly connected by running `./check-refs.sh`
5. Run validation scripts
6. Commit changes (pre-commit hooks will run automatically)
7. Submit a pull request

## Current Status

- ✅ Basic infrastructure and tooling
- ✅ RDF/OWL ontology defined
- ✅ Content authoring pipeline
- ✅ SPARQL endpoint setup
- ✅ CI/CD pipeline
- ✅ Visualization generation
- 🚧 Content creation (8/50 initial nodes)
- 📋 Lean 4 integration (planned)
- 📋 LLM assistance (planned)

## License

This project is licensed under the MIT License - see the LICENSE file for details.

## Acknowledgments

- Built with [Quarto](https://quarto.org/)
- Powered by [Apache Jena](https://jena.apache.org/)
- Inspired by projects like MaRDI and OntoMathPRO

## Contact

For questions or contributions, please open an issue on GitHub.
