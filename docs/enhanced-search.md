# Enhanced Search Functionality

## Overview

The Math Knowledge Graph Wiki now includes enhanced search capabilities that go beyond simple label matching. The new search system combines:

1. **RDF Graph Search**: Exact matching on node labels in the knowledge graph
2. **Full-text Search**: Content search across all mathematical documents using Whoosh
3. **Combined Results**: Merges and ranks results from both sources

## Features

### 1. Full-text Content Search
- Searches the entire content of mathematical definitions, theorems, and examples
- Uses stemming analysis for better matching (e.g., "continuous" matches "continuity")
- Includes fuzzy matching to handle typos

### 2. Search Suggestions
- Provides autocomplete suggestions as you type
- Suggests matching node titles from the knowledge graph
- Helps users discover the correct terminology

### 3. Related Content Discovery
- For each search result, users can explore:
  - **Dependencies**: What concepts this node depends on
  - **Dependents**: What concepts use this node
  - **Examples**: Concrete examples illustrating the concept

### 4. Enhanced Scoring
- Results from both RDF and full-text search are combined
- Nodes found in both sources receive boosted scores
- Results are ranked by relevance

## API Endpoints

### Search Endpoint
```
GET /api/search?q=<query>&limit=<limit>
```

Returns enhanced search results combining RDF and full-text search.

**Example Response:**
```json
{
  "search_term": "continuous",
  "search_type": "enhanced",
  "count": 5,
  "results": [
    {
      "id": "def-continuity",
      "title": "Definition: Continuity",
      "type": "Definition",
      "domain": "Analysis",
      "description": "A function f: A → ℝ is continuous...",
      "sources": ["rdf", "fulltext"],
      "combined_score": 22.5
    }
  ]
}
```

### Search Suggestions Endpoint
```
GET /api/search/suggest?q=<partial_query>&limit=<limit>
```

Returns autocomplete suggestions for partial queries.

### Related Nodes Endpoint
```
GET /api/nodes/<node_id>/related
```

Returns all nodes related to the specified node, categorized by relationship type.

## Implementation Details

### Search Index Building
The search index is built using the Whoosh library:

1. **Indexing**: All `.qmd` files are parsed and indexed
2. **Fields**: Title, content, keywords, description, domain, type
3. **Analysis**: Stemming analyzer for better matching
4. **Keywords**: Automatically extracted from bold, italic, and math terms

### Build Process
The search index is automatically built during the CI/CD pipeline:

```yaml
- name: Build search index
  run: |
    poetry run python scripts/build_search_index.py
```

### Search Algorithm
1. Parse the user query
2. Execute SPARQL query for RDF label matching
3. Execute Whoosh query for full-text matching
4. Merge results, combining scores for duplicates
5. Sort by combined score and return top results

## Usage

### Web Interface
Navigate to the Search page in the Math Knowledge Graph Wiki to use the interactive search interface.

### Programmatic Access
```python
import requests

# Search for content
response = requests.get("http://localhost:5001/api/search?q=group")
results = response.json()

# Get suggestions
response = requests.get("http://localhost:5001/api/search/suggest?q=top")
suggestions = response.json()

# Get related nodes
response = requests.get("http://localhost:5001/api/nodes/def-group/related")
related = response.json()
```

## Performance Considerations

- Search index is stored locally for fast access
- Results are limited to prevent overwhelming responses
- Fuzzy matching is resource-intensive but improves user experience
- Consider implementing caching for frequently searched terms

## Future Enhancements

1. **Caching**: Implement Redis caching for search results
2. **Faceted Search**: Filter by domain, type, or other attributes
3. **Search Analytics**: Track popular searches and improve relevance
4. **Natural Language Queries**: Use LLMs to interpret complex queries
5. **Highlighting**: Show matched terms in context within results
