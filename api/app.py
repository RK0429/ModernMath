"""
Flask REST API for Math Knowledge Graph
Provides endpoints to query and explore the mathematical knowledge graph
"""

from flask import Flask, jsonify, request, abort
from flask_cors import CORS
from pathlib import Path
import sys
from typing import Dict, List, Optional, Any
from SPARQLWrapper import SPARQLWrapper, JSON
import json
import logging

# Add parent directory to path to import scripts
sys.path.append(str(Path(__file__).parent.parent))

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Initialize Flask app
app = Flask(__name__)
CORS(app)  # Enable CORS for all routes

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
def health_check():
    """Health check endpoint"""
    return jsonify({
        "status": "healthy",
        "service": "Math Knowledge Graph API",
        "version": "0.1.0"
    })


@app.route("/api/nodes/<node_id>", methods=["GET"])
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
def search_nodes():
    """Search for nodes by label text"""
    search_term = request.args.get("q", "")
    if not search_term:
        return jsonify({"error": "Search term required"}), 400
    
    query = QUERIES["search_nodes"] % search_term
    results = execute_sparql_query(query)
    
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503
    
    formatted = format_node_response(results)
    formatted["search_term"] = search_term
    return jsonify(formatted)


@app.route("/api/nodes", methods=["GET"])
def get_all_nodes():
    """Get all nodes in the graph"""
    query = QUERIES["get_all_nodes"]
    results = execute_sparql_query(query)
    
    if not results:
        return jsonify({"error": "SPARQL endpoint unavailable"}), 503
    
    return jsonify(format_node_response(results))


@app.route("/api/query", methods=["POST"])
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


@app.errorhandler(404)
def not_found(error):
    """Custom 404 handler"""
    return jsonify({"error": "Endpoint not found"}), 404


@app.errorhandler(500)
def internal_error(error):
    """Custom 500 handler"""
    return jsonify({"error": "Internal server error"}), 500


if __name__ == "__main__":
    # Development server - in production use gunicorn or similar
    app.run(debug=True, host="0.0.0.0", port=5001)