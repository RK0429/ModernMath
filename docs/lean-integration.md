# Lean 4 Integration Documentation

This document describes how formal proofs written in Lean 4 are integrated into the Math Knowledge Graph website.

## Overview

The integration embeds interactive Lean 4 proof editors directly into article pages using iframes that load proofs from the Lean web editor (https://live.lean-lang.org). This allows readers to explore and interact with formal proofs without leaving the article.

## Architecture

### Components

1. **Lean Files**: Located in `/formal/` directory, organized by module
2. **Mapping File**: `lean_mappings.json` links article IDs to Lean proofs
3. **Embedding Script**: `scripts/site/embed_lean_proofs.py` adds proof sections to articles
4. **Progress Pages**: `scripts/site/generate_proof_progress.py` creates tracking pages at `nav/en/proof-progress.qmd` and `nav/ja/proof-progress.qmd`
5. **Build Integration**: GitHub Actions workflow copies Lean files to be served

### How It Works

1. During the build process:
   - The knowledge graph builder reads `lean_mappings.json` and adds `isVerifiedBy` triples
   - The embedding script adds formal proof sections to articles that have verified proofs
   - The progress generator creates overview pages showing verification status
   - Lean files are copied to `_site/formal/` to be served by GitHub Pages

2. When deployed:
   - Articles with formal proofs display an embedded iframe
   - The iframe loads the Lean web editor with the proof file
   - Users can interact with the proof directly in the browser

## Adding New Formal Proofs

### 1. Create the Lean File

Create a new Lean file in the appropriate module directory:

```lean
-- formal/MathKnowledgeGraph/Domain/Module.lean
import Mathlib.Relevant.Module

namespace MathKnowledgeGraph
namespace Domain

/-- Your formalization here -/

end Domain
end MathKnowledgeGraph
```

### 2. Update Mappings

Add an entry to `lean_mappings.json`:

```json
{
  "node_to_lean": {
    "def-your-concept": {
      "lean_id": "Mathlib.Path.To.Definition",
      "module_name": "MathKnowledgeGraph.Domain.Module",
      "quarto_file": "content/domain/def-your-concept.qmd"
    }
  }
}
```

### 3. Build and Deploy

The build process will automatically:

- Detect the new mapping
- Embed the proof section in the article
- Update the progress page
- Deploy the Lean files

## Configuration

### GitHub Pages URL

The embedding script auto-detects the GitHub Pages URL from the git remote. You can override it:

```bash
export GITHUB_PAGES_URL="https://username.github.io/repo"
poetry run python scripts/site/embed_lean_proofs.py
```

### Customizing the Embed

The proof section includes:

- An iframe loading the Lean web editor
- A fullscreen link
- Lean ID and module information

The iframe dimensions and styling can be adjusted in the embedding script.

## Viewing Progress

Navigate to "Formal Proofs" in the site navigation to see:

- Overall verification coverage
- Progress by type (Definition, Theorem, etc.)
- Progress by domain (Algebra, Topology, etc.)
- Detailed status for each article

## Troubleshooting

### Proof Not Showing

1. Check that the article ID in `lean_mappings.json` matches the `id` field in the `.qmd` file
2. Verify the Lean file path is correct
3. Ensure the build workflow completed successfully

### iframe Not Loading

1. Verify the Lean files are being copied to `_site/formal/`
2. Check that the GitHub Pages URL is correct
3. Ensure CORS is not blocking the Lean web editor

### Build Errors

1. Run `poetry run python scripts/site/embed_lean_proofs.py` locally to test
2. Check for syntax errors in `lean_mappings.json`
3. Verify all Lean files exist at the specified paths

## Future Enhancements

- [ ] Add verification status badges to article headers
- [ ] Support for partial proofs and proof sketches
- [ ] Integration with continuous integration for Lean verification
- [ ] Caching of Lean editor state
- [ ] Support for custom Lean environments beyond Mathlib
