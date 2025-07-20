"""
Flask REST API for Math Knowledge Graph
Provides endpoints to query and explore the mathematical knowledge graph
"""

from flask import Flask, jsonify, request, abort
from flask_cors import CORS
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from pathlib import Path
import sys
from typing import Dict, List, Optional, Any
from SPARQLWrapper import SPARQLWrapper, JSON
import json
import logging

# Add parent directory to path to import scripts
sys.path.append(str(Path(__file__).parent.parent))

# Import the enhanced search module
from api.search import MathKnowledgeSearcher
# Import caching module
from api.cache import api_cache, cleanup_cache

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Initialize Flask app
app = Flask(__name__)
CORS(app)  # Enable CORS for all routes

# Initialize rate limiter
limiter = Limiter(
    app=app,
    key_func=get_remote_address,
    default_limits=["200 per day", "50 per hour"],
    storage_uri="memory://",
    headers_enabled=True,  # Include rate limit headers in responses
)

# Configuration
FUSEKI_ENDPOINT = "http://localhost:3030/mathwiki/sparql"
GRAPH_FILE = Path(__file__).parent.parent / "knowledge_graph.ttl"
SEARCH_INDEX_DIR = Path(__file__).parent.parent / "search_index"

# Initialize the enhanced searcher
try:
    searcher = MathKnowledgeSearcher(FUSEKI_ENDPOINT, SEARCH_INDEX_DIR)
    logger.info("Enhanced search initialized successfully")
except Exception as e:
    logger.error(f"Failed to initialize enhanced search: {e}")
    searcher = None

# SPARQL query templates
QUERIES = {
    "get_node": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        
        SELECT ?type ?label ?domain
        FROM <urn:x-arq:DefaultGraph>
        WHERE {
            <https://mathwiki.org/resource/%s> rdf:type ?type ;
                                              rdfs:label ?label .
            OPTIONAL { <https://mathwiki.org/resource/%s> mymath:hasDomain ?domain }
        }
    """,
    
    "get_dependencies": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        
        SELECT ?dependency ?label ?type
        FROM <urn:x-arq:DefaultGraph>
        WHERE {
            <https://mathwiki.org/resource/%s> mymath:uses ?dependency .
            ?dependency rdfs:label ?label ;
                       rdf:type ?type .
        }
    """,
    
    "get_dependents": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        
        SELECT ?dependent ?label ?type
        FROM <urn:x-arq:DefaultGraph>
        WHERE {
            ?dependent mymath:uses <https://mathwiki.org/resource/%s> ;
                      rdfs:label ?label ;
                      rdf:type ?type .
        }
    """,
    
    "search_nodes": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        
        SELECT DISTINCT ?node ?label ?type ?domain
        FROM <urn:x-arq:DefaultGraph>
        WHERE {
            ?node rdfs:label ?label ;
                  rdf:type ?type .
            OPTIONAL { ?node mymath:hasDomain ?domain }
            FILTER(CONTAINS(LCASE(STR(?label)), LCASE("%s")))
        }
        LIMIT 50
    """,
    
    "get_all_nodes": """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        
        SELECT ?node ?label ?type ?domain
        FROM <urn:x-arq:DefaultGraph>
        WHERE {
            ?node rdfs:label ?label ;
                  rdf:type ?type .
            OPTIONAL { ?node mymath:hasDomain ?domain }
            FILTER(?type IN (mymath:Definition, mymath:Theorem, mymath:Axiom, mymath:Example))
        }
        ORDER BY ?label
    """
}


def execute_sparql_query(query: str) -> Optional[Dict[str, Any]]:
    """Execute a SPARQL query against the Fuseki endpoint"""
    try:
        sparql = SPARQLWrapper(FUSEKI_ENDPOINT)
        sparql.setQuery(query)
        sparql.setReturnFormat(JSON)
        return sparql.query().convert()
    except Exception as e:
        logger.error(f"SPARQL query failed: {e}")
        # Fallback to local file parsing if Fuseki is not available
        logger.info("Falling back to local graph file")
        return execute_local_query(query)


def execute_local_query(query: str) -> Optional[Dict[str, Any]]:
    """Execute a query against the local RDF file (fallback when Fuseki is down)"""
    # This is a simplified implementation - in production, you'd use rdflib
    # For now, return a message indicating Fuseki is required
    return None


def extract_node_id(uri: str) -> str:
    """Extract the node ID from a full URI"""
    return uri.split("/")[-1]


def format_node_response(results: Dict[str, Any]) -> Dict[str, Any]:
    """Format SPARQL results into a clean JSON response"""
    if not results or "results" not in results:
        return {"error": "No results found"}
    
    bindings = results["results"]["bindings"]
    if not bindings:
        return {"error": "Node not found"}
    
    # Process results
    formatted = []
    for binding in bindings:
        item = {}
        for key, value in binding.items():
            if value["type"] == "uri":
                # Extract local part of URI for cleaner output
                item[key] = value["value"].split("#")[-1] if "#" in value["value"] else value["value"]
            else:
                item[key] = value["value"]
        formatted.append(item)
    
    return {"results": formatted, "count": len(formatted)}


@app.route("/api/health", methods=["GET"])
@limiter.limit("100 per minute")
def health_check():
    """Health check endpoint"""
    return jsonify({
        "status": "healthy",
        "service": "Math Knowledge Graph API",
        "version": "0.1.0"
    })


@app.route("/api/nodes/<node_id>", methods=["GET"])
@limiter.limit("30 per minute")
@api_cache(ttl=600)  # Cache for 10 minutes
def get_node(node_id: str):
    """Get details about a specific node"""
    query = QUERIES["get_node"] % (node_id, node_id)
    results = execute_sparql_query(query)
    
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503
    
    formatted = format_node_response(results)
    if "error" in formatted:
        return jsonify(formatted), 404
    
    # Add the node ID to the response
    formatted["node_id"] = node_id
    return jsonify(formatted)


@app.route("/api/dependencies/<node_id>", methods=["GET"])
@limiter.limit("30 per minute")
@api_cache(ttl=600)  # Cache for 10 minutes
def get_dependencies(node_id: str):
    """Get all nodes that this node depends on (uses)"""
    query = QUERIES["get_dependencies"] % node_id
    results = execute_sparql_query(query)
    
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503
    
    formatted = format_node_response(results)
    formatted["node_id"] = node_id
    formatted["relationship"] = "uses"
    return jsonify(formatted)


@app.route("/api/dependents/<node_id>", methods=["GET"])
@limiter.limit("30 per minute")
@api_cache(ttl=600)  # Cache for 10 minutes
def get_dependents(node_id: str):
    """Get all nodes that depend on (use) this node"""
    query = QUERIES["get_dependents"] % node_id
    results = execute_sparql_query(query)
    
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503
    
    formatted = format_node_response(results)
    formatted["node_id"] = node_id
    formatted["relationship"] = "used_by"
    return jsonify(formatted)


@app.route("/api/search", methods=["GET"])
@limiter.limit("20 per minute")
@api_cache(ttl=300)  # Cache for 5 minutes
def search_nodes():
    """Enhanced search for nodes by label text and content"""
    search_term = request.args.get("q", "")
    if not search_term:
        return jsonify({"error": "Search term required"}), 400
    
    # Check if enhanced search is available
    if searcher is None:
        # Fall back to basic SPARQL search
        query = QUERIES["search_nodes"] % search_term
        results = execute_sparql_query(query)
        
        if not results:
            return jsonify({"error": "SPARQL endpoint unavailable"}), 503
        
        formatted = format_node_response(results)
        formatted["search_term"] = search_term
        formatted["search_type"] = "basic"
        return jsonify(formatted)
    
    # Use enhanced search
    try:
        # Get limit parameter
        limit = request.args.get("limit", default=50, type=int)
        limit = min(limit, 100)  # Cap at 100 results
        
        # Perform combined search
        results = searcher.search_combined(search_term, limit=limit)
        
        return jsonify({
            "search_term": search_term,
            "search_type": "enhanced",
            "count": len(results),
            "results": results
        })
        
    except Exception as e:
        logger.error(f"Enhanced search failed: {e}")
        # Fall back to basic search
        query = QUERIES["search_nodes"] % search_term
        results = execute_sparql_query(query)
        
        if not results:
            return jsonify({"error": "Search failed"}), 503
        
        formatted = format_node_response(results)
        formatted["search_term"] = search_term
        formatted["search_type"] = "basic_fallback"
        return jsonify(formatted)


@app.route("/api/nodes", methods=["GET"])
@limiter.limit("10 per minute")
@api_cache(ttl=900)  # Cache for 15 minutes
def get_all_nodes():
    """Get all nodes in the graph"""
    query = QUERIES["get_all_nodes"]
    results = execute_sparql_query(query)
    
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503
    
    return jsonify(format_node_response(results))


@app.route("/api/query", methods=["POST"])
@limiter.limit("5 per minute")
def custom_query():
    """Execute a custom SPARQL query (with restrictions for safety)"""
    data = request.get_json()
    if not data or "query" not in data:
        return jsonify({"error": "Query required in request body"}), 400
    
    query = data["query"]
    
    # Basic safety check - only allow SELECT queries
    if not query.strip().upper().startswith("SELECT"):
        return jsonify({"error": "Only SELECT queries are allowed"}), 400
    
    # Additional safety checks could be added here
    
    results = execute_sparql_query(query)
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503
    
    return jsonify(results)


@app.route("/api/search/suggest", methods=["GET"])
@limiter.limit("60 per minute")
@api_cache(ttl=300)  # Cache for 5 minutes
def search_suggestions():
    """Get search suggestions for autocomplete"""
    partial_query = request.args.get("q", "")
    if not partial_query or len(partial_query) < 2:
        return jsonify({"suggestions": []})
    
    if searcher is None:
        return jsonify({"error": "Search suggestions unavailable"}), 503
    
    try:
        limit = request.args.get("limit", default=10, type=int)
        limit = min(limit, 20)  # Cap at 20 suggestions
        
        suggestions = searcher.suggest_search_terms(partial_query, limit=limit)
        
        return jsonify({
            "query": partial_query,
            "suggestions": suggestions
        })
        
    except Exception as e:
        logger.error(f"Search suggestions failed: {e}")
        return jsonify({"suggestions": []})


@app.route("/api/nodes/<node_id>/related", methods=["GET"])
@limiter.limit("20 per minute")
@api_cache(ttl=600)  # Cache for 10 minutes
def get_related_nodes(node_id: str):
    """Get all nodes related to the specified node"""
    if searcher is None:
        return jsonify({"error": "Related nodes search unavailable"}), 503
    
    try:
        related = searcher.get_related_nodes(node_id)
        
        return jsonify({
            "node_id": node_id,
            "related": related
        })
        
    except Exception as e:
        logger.error(f"Related nodes search failed: {e}")
        return jsonify({"error": "Failed to get related nodes"}), 500


@app.route("/api/cache/clear", methods=["POST"])
@limiter.limit("1 per hour")
def clear_cache():
    """Clear all cached responses (requires admin access in production)"""
    try:
        from api.cache import _cache
        _cache.clear()
        logger.info("Cache cleared successfully")
        return jsonify({"message": "Cache cleared successfully"})
    except Exception as e:
        logger.error(f"Failed to clear cache: {e}")
        return jsonify({"error": "Failed to clear cache"}), 500


@app.route("/api/cache/stats", methods=["GET"])
@limiter.limit("10 per minute")
def cache_stats():
    """Get cache statistics"""
    try:
        from api.cache import _cache
        # Count non-expired entries
        _cache.cleanup_expired()
        cache_size = len(_cache._cache)
        return jsonify({
            "cache_entries": cache_size,
            "status": "operational"
        })
    except Exception as e:
        logger.error(f"Failed to get cache stats: {e}")
        return jsonify({"error": "Failed to get cache stats"}), 500


# Background thread for periodic cache cleanup
def start_cache_cleanup():
    """Start background thread for periodic cache cleanup"""
    import threading
    import time
    
    def cleanup_loop():
        while True:
            time.sleep(300)  # Run every 5 minutes
            try:
                cleanup_cache()
                logger.debug("Cache cleanup completed")
            except Exception as e:
                logger.error(f"Cache cleanup failed: {e}")
    
    cleanup_thread = threading.Thread(target=cleanup_loop, daemon=True)
    cleanup_thread.start()
    logger.info("Cache cleanup thread started")


@app.errorhandler(404)
def not_found(error):
    """Custom 404 handler"""
    return jsonify({"error": "Endpoint not found"}), 404


@app.errorhandler(429)
def rate_limit_exceeded(error):
    """Custom handler for rate limit exceeded"""
    return jsonify({
        "error": "Rate limit exceeded",
        "message": str(error.description),
        "retry_after": error.description.get_headers().get("Retry-After", "60")
    }), 429


@app.errorhandler(500)
def internal_error(error):
    """Custom 500 handler"""
    return jsonify({"error": "Internal server error"}), 500


if __name__ == "__main__":
    # Start cache cleanup thread
    start_cache_cleanup()
    
    # Development server - in production use gunicorn or similar
    app.run(debug=True, host="0.0.0.0", port=5001)