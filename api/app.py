"""
Flask REST API for Math Knowledge Graph
Provides endpoints to query and explore the mathematical knowledge graph
"""

# mypy: disable-error-code=misc

import logging
import sys
import threading
import time
from pathlib import Path
from typing import Dict, Optional, Any

from flask import Flask, jsonify, request
from flask_cors import CORS
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from flask_limiter.errors import RateLimitExceeded
from SPARQLWrapper import SPARQLWrapper, JSON
from SPARQLWrapper.SPARQLExceptions import SPARQLWrapperException

from cache import api_cache, cleanup_cache, _cache

# Add parent directory to path to import scripts
sys.path.append(str(Path(__file__).parent.parent))

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
    """,
}


def execute_sparql_query(query: str) -> Optional[Dict[str, Any]]:
    """Execute a SPARQL query against the Fuseki endpoint"""
    try:
        sparql = SPARQLWrapper(FUSEKI_ENDPOINT)
        sparql.setQuery(query)
        sparql.setReturnFormat(JSON)
        result = sparql.query().convert()
        # SPARQLWrapper returns various types, we cast to Dict for type safety
        return result  # type: ignore[no-any-return]
    except SPARQLWrapperException as e:
        logger.error("SPARQL query failed: %s", e)
        # Fallback to local file parsing if Fuseki is not available
        logger.info("Falling back to local graph file")
        return execute_local_query(query)


def execute_local_query(query: str) -> Optional[Dict[str, Any]]:  # pylint: disable=useless-return
    """Execute a query against the local RDF file (fallback when Fuseki is down)"""
    # This is a simplified implementation - in production, you'd use rdflib
    # For now, return a message indicating Fuseki is required
    _ = query  # Mark parameter as used
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
                item[key] = (
                    value["value"].split("#")[-1] if "#" in value["value"] else value["value"]
                )
            else:
                item[key] = value["value"]
        formatted.append(item)

    return {"results": formatted, "count": len(formatted)}


@app.route("/api/health", methods=["GET"])
@limiter.limit("100 per minute")
def health_check() -> tuple[Any, int]:
    """Health check endpoint"""
    return (
        jsonify({"status": "healthy", "service": "Math Knowledge Graph API", "version": "0.1.0"}),
        200,
    )


@app.route("/api/nodes/<node_id>", methods=["GET"])
@limiter.limit("30 per minute")
@api_cache(ttl=600)  # Cache for 10 minutes
def get_node(node_id: str) -> tuple[Any, int]:
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
    return jsonify(formatted), 200


@app.route("/api/dependencies/<node_id>", methods=["GET"])
@limiter.limit("30 per minute")
@api_cache(ttl=600)  # Cache for 10 minutes
def get_dependencies(node_id: str) -> tuple[Any, int]:
    """Get all nodes that this node depends on (uses)"""
    query = QUERIES["get_dependencies"] % node_id
    results = execute_sparql_query(query)

    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503

    formatted = format_node_response(results)
    formatted["node_id"] = node_id
    formatted["relationship"] = "uses"
    return jsonify(formatted), 200


@app.route("/api/dependents/<node_id>", methods=["GET"])
@limiter.limit("30 per minute")
@api_cache(ttl=600)  # Cache for 10 minutes
def get_dependents(node_id: str) -> tuple[Any, int]:
    """Get all nodes that depend on (use) this node"""
    query = QUERIES["get_dependents"] % node_id
    results = execute_sparql_query(query)

    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503

    formatted = format_node_response(results)
    formatted["node_id"] = node_id
    formatted["relationship"] = "used_by"
    return jsonify(formatted), 200


@app.route("/api/search", methods=["GET"])
@limiter.limit("20 per minute")
@api_cache(ttl=300)  # Cache for 5 minutes
def search_nodes() -> tuple[Any, int]:
    """Search for nodes by label text using SPARQL"""
    search_term = request.args.get("q", "")
    if not search_term:
        return jsonify({"error": "Search term required"}), 400

    # Use basic SPARQL search
    query = QUERIES["search_nodes"] % search_term
    results = execute_sparql_query(query)

    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503

    formatted = format_node_response(results)
    formatted["search_term"] = search_term
    formatted["search_type"] = "sparql"
    return jsonify(formatted), 200


@app.route("/api/nodes", methods=["GET"])
@limiter.limit("10 per minute")
@api_cache(ttl=900)  # Cache for 15 minutes
def get_all_nodes() -> tuple[Any, int]:
    """Get all nodes in the graph"""
    query = QUERIES["get_all_nodes"]
    results = execute_sparql_query(query)

    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503

    return jsonify(format_node_response(results)), 200


@app.route("/api/query", methods=["POST"])
@limiter.limit("5 per minute")
def custom_query() -> tuple[Any, int]:
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

    return jsonify(results), 200


@app.route("/api/cache/clear", methods=["POST"])
@limiter.limit("1 per hour")
def clear_cache() -> tuple[Any, int]:
    """Clear all cached responses (requires admin access in production)"""
    try:
        _cache.clear()
        logger.info("Cache cleared successfully")
        return jsonify({"message": "Cache cleared successfully"}), 200
    except (ImportError, AttributeError) as e:
        logger.error("Failed to clear cache: %s", e)
        return jsonify({"error": "Failed to clear cache"}), 500


@app.route("/api/cache/stats", methods=["GET"])
@limiter.limit("10 per minute")
def cache_stats() -> tuple[Any, int]:
    """Get cache statistics"""
    try:
        # Count non-expired entries
        _cache.cleanup_expired()
        cache_size = len(_cache._cache)  # pylint: disable=protected-access
        return jsonify({"cache_entries": cache_size, "status": "operational"}), 200
    except (ImportError, AttributeError) as e:
        logger.error("Failed to get cache stats: %s", e)
        return jsonify({"error": "Failed to get cache stats"}), 500


# Background thread for periodic cache cleanup
def start_cache_cleanup() -> None:
    """Start background thread for periodic cache cleanup"""

    def cleanup_loop() -> None:
        while True:
            time.sleep(300)  # Run every 5 minutes
            try:
                cleanup_cache()
                logger.debug("Cache cleanup completed")
            except (ImportError, AttributeError) as e:
                logger.error("Cache cleanup failed: %s", e)

    cleanup_thread = threading.Thread(target=cleanup_loop, daemon=True)
    cleanup_thread.start()
    logger.info("Cache cleanup thread started")


@app.errorhandler(404)
def not_found(error: Any) -> tuple[Any, int]:
    """Custom 404 handler"""
    _ = error  # Mark parameter as used
    return jsonify({"error": "Endpoint not found"}), 404


@app.errorhandler(RateLimitExceeded)
def rate_limit_exceeded(error: RateLimitExceeded) -> tuple[Any, int]:
    """Custom handler for rate limit exceeded"""
    # Extract retry-after from headers list
    retry_after = "60"
    for header, value in error.get_headers():
        if header == "Retry-After":
            retry_after = value
            break

    return (
        jsonify(
            {
                "error": "Rate limit exceeded",
                "message": error.description,
                "retry_after": retry_after,
            }
        ),
        429,
    )


@app.errorhandler(500)
def internal_error(error: Any) -> tuple[Any, int]:
    """Custom 500 handler"""
    _ = error  # Mark parameter as used
    return jsonify({"error": "Internal server error"}), 500


if __name__ == "__main__":
    # Start cache cleanup thread
    start_cache_cleanup()

    # Development server - in production use gunicorn or similar
    app.run(debug=True, host="0.0.0.0", port=5001)
