"""
Enhanced search functionality combining RDF graph search and full-text search.
"""

import logging
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from collections import defaultdict

from whoosh import index
from whoosh.qparser import MultifieldParser, FuzzyTermPlugin, OrGroup
from whoosh.qparser.syntax import AndGroup
from SPARQLWrapper import SPARQLWrapper, JSON

logger = logging.getLogger(__name__)


class MathKnowledgeSearcher:
    """Combined search across RDF graph and full-text index"""
    
    def __init__(self, fuseki_endpoint: str, index_dir: Path):
        self.fuseki_endpoint = fuseki_endpoint
        self.index_dir = index_dir
        
        # Open the Whoosh index
        if not index_dir.exists():
            raise ValueError(f"Search index directory {index_dir} does not exist")
        
        self.ix = index.open_dir(str(index_dir))
        
        # Create parser for full-text search
        self.parser = MultifieldParser(
            ["title", "content", "keywords", "description"],
            self.ix.schema,
            group=OrGroup  # Use OR by default for more results
        )
        self.parser.add_plugin(FuzzyTermPlugin())
    
    def search_rdf_graph(self, query: str, limit: int = 20) -> List[Dict]:
        """Search the RDF graph for nodes matching the query"""
        sparql_query = f"""
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        
        SELECT DISTINCT ?node ?label ?type ?domain
        FROM <urn:x-arq:DefaultGraph>
        WHERE {{
            ?node rdfs:label ?label ;
                  rdf:type ?type .
            OPTIONAL {{ ?node mymath:hasDomain ?domain }}
            FILTER(CONTAINS(LCASE(STR(?label)), LCASE("{query}")))
        }}
        LIMIT {limit}
        """
        
        try:
            sparql = SPARQLWrapper(self.fuseki_endpoint)
            sparql.setQuery(sparql_query)
            sparql.setReturnFormat(JSON)
            results = sparql.query().convert()
            
            rdf_results = []
            for binding in results["results"]["bindings"]:
                node_uri = binding["node"]["value"]
                node_id = node_uri.split("/")[-1]
                
                rdf_results.append({
                    'id': node_id,
                    'title': binding["label"]["value"],
                    'type': binding["type"]["value"].split("#")[-1],
                    'domain': binding.get("domain", {}).get("value", ""),
                    'source': 'rdf',
                    'score': 1.0  # RDF matches are exact
                })
            
            return rdf_results
            
        except Exception as e:
            logger.error(f"RDF search failed: {e}")
            return []
    
    def search_full_text(self, query: str, limit: int = 20) -> List[Dict]:
        """Search the full-text index"""
        try:
            parsed_query = self.parser.parse(query)
            
            results = []
            with self.ix.searcher() as searcher:
                hits = searcher.search(parsed_query, limit=limit)
                
                for hit in hits:
                    results.append({
                        'id': hit['id'],
                        'title': hit['title'],
                        'type': hit['type'],
                        'domain': hit['domain'],
                        'path': hit['path'],
                        'description': hit.get('description', ''),
                        'source': 'fulltext',
                        'score': hit.score
                    })
            
            return results
            
        except Exception as e:
            logger.error(f"Full-text search failed: {e}")
            return []
    
    def search_combined(self, query: str, limit: int = 50) -> List[Dict]:
        """
        Perform a combined search across both RDF graph and full-text index.
        Results are merged and ranked by relevance.
        """
        # Get results from both sources
        rdf_results = self.search_rdf_graph(query, limit=limit)
        fulltext_results = self.search_full_text(query, limit=limit)
        
        # Merge results, combining scores for duplicates
        combined = {}
        
        # Process RDF results first (they have exact matches)
        for result in rdf_results:
            result_id = result['id']
            combined[result_id] = result.copy()
            combined[result_id]['sources'] = ['rdf']
            combined[result_id]['combined_score'] = result['score'] * 2  # Boost RDF matches
        
        # Process full-text results
        for result in fulltext_results:
            result_id = result['id']
            if result_id in combined:
                # Merge with existing result
                combined[result_id]['sources'].append('fulltext')
                combined[result_id]['combined_score'] += result['score']
                # Add description if not present
                if 'description' not in combined[result_id] and 'description' in result:
                    combined[result_id]['description'] = result['description']
                if 'path' not in combined[result_id] and 'path' in result:
                    combined[result_id]['path'] = result['path']
            else:
                # New result from full-text only
                combined[result_id] = result.copy()
                combined[result_id]['sources'] = ['fulltext']
                combined[result_id]['combined_score'] = result['score']
        
        # Sort by combined score
        sorted_results = sorted(
            combined.values(),
            key=lambda x: x['combined_score'],
            reverse=True
        )
        
        # Return top results up to limit
        return sorted_results[:limit]
    
    def get_related_nodes(self, node_id: str) -> Dict[str, List[Dict]]:
        """Get nodes related to a given node (dependencies and dependents)"""
        related = {
            'dependencies': [],
            'dependents': [],
            'examples': [],
            'see_also': []
        }
        
        # Query for dependencies (nodes this one uses)
        deps_query = f"""
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        PREFIX base: <https://mathwiki.org/resource/>
        
        SELECT ?dep ?label ?type
        FROM <urn:x-arq:DefaultGraph>
        WHERE {{
            base:{node_id} mymath:uses ?dep .
            ?dep rdfs:label ?label ;
                 rdf:type ?type .
        }}
        """
        
        # Query for dependents (nodes that use this one)
        dependents_query = f"""
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        PREFIX base: <https://mathwiki.org/resource/>
        
        SELECT ?dependent ?label ?type
        FROM <urn:x-arq:DefaultGraph>
        WHERE {{
            ?dependent mymath:uses base:{node_id} ;
                       rdfs:label ?label ;
                       rdf:type ?type .
        }}
        """
        
        try:
            sparql = SPARQLWrapper(self.fuseki_endpoint)
            
            # Get dependencies
            sparql.setQuery(deps_query)
            sparql.setReturnFormat(JSON)
            deps_results = sparql.query().convert()
            
            for binding in deps_results["results"]["bindings"]:
                dep_uri = binding["dep"]["value"]
                dep_id = dep_uri.split("/")[-1]
                dep_type = binding["type"]["value"].split("#")[-1]
                related['dependencies'].append({
                    'id': dep_id,
                    'title': binding["label"]["value"],
                    'type': dep_type
                })
            
            # Get dependents
            sparql.setQuery(dependents_query)
            sparql.setReturnFormat(JSON)
            dependents_results = sparql.query().convert()
            
            for binding in dependents_results["results"]["bindings"]:
                dep_uri = binding["dependent"]["value"]
                dep_id = dep_uri.split("/")[-1]
                node_type = binding["type"]["value"].split("#")[-1]
                
                # Separate examples from other dependents
                if node_type == "Example":
                    related['examples'].append({
                        'id': dep_id,
                        'title': binding["label"]["value"],
                        'type': node_type
                    })
                else:
                    related['dependents'].append({
                        'id': dep_id,
                        'title': binding["label"]["value"],
                        'type': node_type
                    })
            
            return related
            
        except Exception as e:
            logger.error(f"Failed to get related nodes: {e}")
            return related
    
    def suggest_search_terms(self, partial_query: str, limit: int = 10) -> List[str]:
        """Provide search suggestions based on partial query"""
        suggestions = set()
        
        # Search titles that start with the partial query
        with self.ix.searcher() as searcher:
            # Use prefix query for title field
            from whoosh.query import Prefix
            prefix_query = Prefix("title", partial_query.lower())
            
            results = searcher.search(prefix_query, limit=limit)
            for hit in results:
                suggestions.add(hit['title'])
        
        # Also check RDF labels
        sparql_query = f"""
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        
        SELECT DISTINCT ?label
        FROM <urn:x-arq:DefaultGraph>
        WHERE {{
            ?node rdfs:label ?label .
            FILTER(STRSTARTS(LCASE(?label), LCASE("{partial_query}")))
        }}
        LIMIT {limit}
        """
        
        try:
            sparql = SPARQLWrapper(self.fuseki_endpoint)
            sparql.setQuery(sparql_query)
            sparql.setReturnFormat(JSON)
            results = sparql.query().convert()
            
            for binding in results["results"]["bindings"]:
                suggestions.add(binding["label"]["value"])
                
        except Exception as e:
            logger.error(f"Failed to get suggestions from RDF: {e}")
        
        return sorted(list(suggestions))[:limit]