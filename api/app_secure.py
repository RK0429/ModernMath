"""
Flask REST API for Math Knowledge Graph - Enhanced Security Version
Provides endpoints to query and explore the mathematical knowledge graph
with improved security features including authentication, input validation,
and query complexity limits.
"""

from flask import Flask, jsonify, request, abort
from flask_cors import CORS
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from flask_limiter.errors import RateLimitExceeded
from pathlib import Path
import sys
from typing import Dict, List, Optional, Any
from SPARQLWrapper import SPARQLWrapper, JSON
import json
import logging
import os

# Add parent directory to path to import scripts
sys.path.append(str(Path(__file__).parent.parent))

# Import the enhanced search module
from api.search import MathKnowledgeSearcher
# Import caching module
from api.cache import api_cache, cleanup_cache
# Import security utilities
from api.security import (
    require_auth, validate_sparql_query, validate_node_id, 
    validate_search_term, sanitize_output
)
# Import monitoring utilities
from api.monitoring import (
    init_monitoring, monitor_request, monitor_sparql_query,
    structured_logger, metrics_collector, HealthChecker
)

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Initialize Flask app
app = Flask(__name__)

# Initialize monitoring
init_monitoring(app)

# Configure CORS with specific origins and methods
CORS(app, 
     origins=[
         "http://localhost:*",
         "https://rk0429.github.io",
         "https://*.github.io"
     ],
     methods=["GET", "POST", "OPTIONS"],
     allow_headers=["Content-Type", "Authorization"],
     max_age=3600
)

# Initialize rate limiter with Redis backend for production
limiter = Limiter(
    app=app,
    key_func=get_remote_address,
    default_limits=["200 per day", "50 per hour"],
    storage_uri=os.environ.get('REDIS_URL', 'memory://'),
    headers_enabled=True,
)

# Configuration
FUSEKI_ENDPOINT = os.environ.get('FUSEKI_ENDPOINT', 'http://localhost:3030/mathwiki/sparql')
GRAPH_FILE = Path(__file__).parent.parent / "knowledge_graph.ttl"
SEARCH_INDEX_DIR = Path(__file__).parent.parent / "search_index"

# Initialize the enhanced searcher
try:
    searcher = MathKnowledgeSearcher(FUSEKI_ENDPOINT, SEARCH_INDEX_DIR)
    logger.info("Enhanced search initialized successfully")
except Exception as e:
    logger.error(f"Failed to initialize enhanced search: {e}")
    searcher = None

# SPARQL query templates with parameterized queries for safety
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
        LIMIT 10
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
        LIMIT 100
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
        LIMIT 100
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
        LIMIT 1000
    """
}


@monitor_sparql_query("general")
def execute_sparql_query(query: str) -> Optional[Dict[str, Any]]:
    """Execute a SPARQL query against the Fuseki endpoint with timeout"""
    try:
        sparql = SPARQLWrapper(FUSEKI_ENDPOINT)
        sparql.setQuery(query)
        sparql.setReturnFormat(JSON)
        sparql.setTimeout(10)  # 10 second timeout
        return sparql.query().convert()
    except Exception as e:
        logger.error(f"SPARQL query failed: {e}")
        return None


def format_node_response(results: Dict[str, Any]) -> Dict[str, Any]:
    """Format SPARQL results into a clean JSON response with sanitization"""
    if not results or "results" not in results:
        return {"error": "No results found"}
    
    bindings = results["results"]["bindings"]
    if not bindings:
        return {"error": "Node not found"}
    
    # Process results with output sanitization
    formatted = []
    for binding in bindings:
        item = {}
        for key, value in binding.items():
            if value["type"] == "uri":
                # Extract local part of URI for cleaner output
                item[key] = value["value"].split("#")[-1] if "#" in value["value"] else value["value"]
            else:
                item[key] = sanitize_output(value["value"])
        formatted.append(item)
    
    return {"results": formatted, "count": len(formatted)}


@app.route("/api/health", methods=["GET"])
@limiter.limit("100 per minute")
def health_check():
    """Health check endpoint"""
    return jsonify({
        "status": "healthy",
        "service": "Math Knowledge Graph API",
        "version": "0.2.0",
        "security": "enhanced"
    })


@app.route("/api/nodes/<node_id>", methods=["GET"])
@limiter.limit("30 per minute")
@api_cache(ttl=600)
def get_node(node_id: str):
    """Get details about a specific node with input validation"""
    # Validate node ID
    if not validate_node_id(node_id):
        return jsonify({"error": "Invalid node ID format"}), 400
    
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
@api_cache(ttl=600)
def get_dependencies(node_id: str):
    """Get all nodes that this node depends on (uses) with validation"""
    # Validate node ID
    if not validate_node_id(node_id):
        return jsonify({"error": "Invalid node ID format"}), 400
    
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
@api_cache(ttl=600)
def get_dependents(node_id: str):
    """Get all nodes that depend on (use) this node with validation"""
    # Validate node ID
    if not validate_node_id(node_id):
        return jsonify({"error": "Invalid node ID format"}), 400
    
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
@api_cache(ttl=300)
def search_nodes():
    """Enhanced search for nodes with input validation"""
    search_term = request.args.get("q", "")
    
    # Validate search term
    if not search_term:
        return jsonify({"error": "Search term required"}), 400
    
    if not validate_search_term(search_term):
        return jsonify({"error": "Invalid search term"}), 400
    
    # Check if enhanced search is available
    if searcher is None:
        # Fall back to basic SPARQL search
        query = QUERIES["search_nodes"] % search_term
        results = execute_sparql_query(query)
        
        if not results:
            return jsonify({"error": "SPARQL endpoint unavailable"}), 503
        
        formatted = format_node_response(results)
        formatted["search_term"] = sanitize_output(search_term)
        formatted["search_type"] = "basic"
        return jsonify(formatted)
    
    # Use enhanced search
    try:
        # Get limit parameter with validation
        limit = request.args.get("limit", default=50, type=int)
        limit = min(max(limit, 1), 100)  # Clamp between 1 and 100
        
        # Perform combined search
        results = searcher.search_combined(search_term, limit=limit)
        
        return jsonify({
            "search_term": sanitize_output(search_term),
            "search_type": "enhanced",
            "count": len(results),
            "results": sanitize_output(results)
        })
        
    except Exception as e:
        logger.error(f"Enhanced search failed: {e}")
        return jsonify({"error": "Search failed"}), 500


@app.route("/api/nodes", methods=["GET"])
@limiter.limit("10 per minute")
@api_cache(ttl=900)
def get_all_nodes():
    """Get all nodes in the graph with pagination support"""
    # Add pagination parameters
    page = request.args.get("page", default=1, type=int)
    per_page = request.args.get("per_page", default=100, type=int)
    
    # Validate pagination parameters
    page = max(page, 1)
    per_page = min(max(per_page, 1), 200)  # Max 200 items per page
    
    offset = (page - 1) * per_page
    
    # Modified query with pagination
    paginated_query = QUERIES["get_all_nodes"].replace("LIMIT 1000", f"LIMIT {per_page} OFFSET {offset}")
    
    results = execute_sparql_query(paginated_query)
    
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503
    
    formatted = format_node_response(results)
    formatted["page"] = page
    formatted["per_page"] = per_page
    return jsonify(formatted)


@app.route("/api/query", methods=["POST"])
@limiter.limit("5 per minute")
def custom_query():
    """Execute a custom SPARQL query with comprehensive validation"""
    data = request.get_json()
    if not data or "query" not in data:
        return jsonify({"error": "Query required in request body"}), 400
    
    query = data["query"]
    
    # Validate query for safety and complexity
    is_valid, error_message = validate_sparql_query(query)
    if not is_valid:
        return jsonify({"error": error_message}), 400
    
    # Add timeout to query execution
    results = execute_sparql_query(query)
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable or query timeout"}), 503
    
    # Sanitize output
    return jsonify(sanitize_output(results))


@app.route("/api/auth/login", methods=["POST"])
@limiter.limit("5 per minute")
def login():
    """Login endpoint for obtaining authentication token"""
    data = request.get_json()
    
    if not data or "username" not in data or "password" not in data:
        return jsonify({"error": "Username and password required"}), 400
    
    # In production, verify against a user database
    # For now, we'll use a simple check
    if data["username"] == "admin" and data["password"] == os.environ.get("ADMIN_PASSWORD", "change-me"):
        from api.security import generate_token
        token = generate_token(data["username"])
        return jsonify({"token": token})
    
    return jsonify({"error": "Invalid credentials"}), 401


# Example protected endpoint for future write operations
@app.route("/api/admin/reload-graph", methods=["POST"])
@limiter.limit("1 per hour")
@require_auth
def reload_graph():
    """Protected endpoint to reload the knowledge graph (requires authentication)"""
    try:
        # In production, this would trigger a graph reload
        # For now, just return success
        return jsonify({
            "message": "Graph reload initiated",
            "user": request.user["user_id"]
        })
    except Exception as e:
        logger.error(f"Graph reload failed: {e}")
        return jsonify({"error": "Graph reload failed"}), 500


@app.route("/api/search/suggest", methods=["GET"])
@limiter.limit("60 per minute")
@api_cache(ttl=300)
def search_suggestions():
    """Get search suggestions with validation"""
    partial_query = request.args.get("q", "")
    
    if not partial_query or len(partial_query) < 2:
        return jsonify({"suggestions": []})
    
    if not validate_search_term(partial_query):
        return jsonify({"error": "Invalid search query"}), 400
    
    if searcher is None:
        return jsonify({"error": "Search suggestions unavailable"}), 503
    
    try:
        limit = request.args.get("limit", default=10, type=int)
        limit = min(max(limit, 1), 20)  # Clamp between 1 and 20
        
        suggestions = searcher.suggest_search_terms(partial_query, limit=limit)
        
        return jsonify({
            "query": sanitize_output(partial_query),
            "suggestions": sanitize_output(suggestions)
        })
        
    except Exception as e:
        logger.error(f"Search suggestions failed: {e}")
        return jsonify({"suggestions": []})


@app.route("/api/cache/clear", methods=["POST"])
@limiter.limit("1 per hour")
@require_auth
def clear_cache():
    """Clear all cached responses (requires authentication)"""
    try:
        from api.cache import _cache
        _cache.clear()
        logger.info(f"Cache cleared by user: {request.user['user_id']}")
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
        _cache.cleanup_expired()
        cache_size = len(_cache._cache)
        return jsonify({
            "cache_entries": cache_size,
            "status": "operational"
        })
    except Exception as e:
        logger.error(f"Failed to get cache stats: {e}")
        return jsonify({"error": "Failed to get cache stats"}), 500


# Error handlers
@app.errorhandler(404)
def not_found(error):
    """Custom 404 handler"""
    return jsonify({"error": "Endpoint not found"}), 404


@app.errorhandler(RateLimitExceeded)
def rate_limit_exceeded(error):
    """Custom handler for rate limit exceeded"""
    retry_after = "60"
    for header, value in error.get_headers():
        if header == "Retry-After":
            retry_after = value
            break
    
    return jsonify({
        "error": "Rate limit exceeded",
        "message": error.description,
        "retry_after": retry_after
    }), 429


@app.errorhandler(400)
def bad_request(error):
    """Custom 400 handler"""
    return jsonify({"error": "Bad request"}), 400


@app.errorhandler(500)
def internal_error(error):
    """Custom 500 handler"""
    logger.error(f"Internal server error: {error}")
    return jsonify({"error": "Internal server error"}), 500


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


if __name__ == "__main__":
    # Start cache cleanup thread
    start_cache_cleanup()
    
    # Production server configuration
    if os.environ.get("FLASK_ENV") == "production":
        app.run(host="0.0.0.0", port=5001, debug=False)
    else:
        # Development server
        app.run(debug=True, host="0.0.0.0", port=5001)