"""
Security utilities for the Math Knowledge Graph API
Provides authentication, validation, and query complexity checking
"""

import re
import functools
from typing import Dict, Any, Optional, Callable
from flask import request, jsonify
import jwt
from datetime import datetime, timedelta
import os


# JWT Configuration
JWT_SECRET_KEY = os.environ.get("JWT_SECRET_KEY", "your-secret-key-change-in-production")
JWT_ALGORITHM = "HS256"
JWT_EXPIRATION_DELTA = timedelta(hours=24)


def generate_token(user_id: str) -> str:
    """Generate a JWT token for authentication"""
    payload = {
        "user_id": user_id,
        "exp": datetime.utcnow() + JWT_EXPIRATION_DELTA,
        "iat": datetime.utcnow(),
    }
    return jwt.encode(payload, JWT_SECRET_KEY, algorithm=JWT_ALGORITHM)


def verify_token(token: str) -> Optional[Dict[str, Any]]:
    """Verify and decode a JWT token"""
    try:
        payload = jwt.decode(token, JWT_SECRET_KEY, algorithms=[JWT_ALGORITHM])
        return payload
    except jwt.ExpiredSignatureError:
        return None
    except jwt.InvalidTokenError:
        return None


def require_auth(f: Callable) -> Callable:
    """Decorator to require authentication for write operations"""

    @functools.wraps(f)
    def decorated_function(*args, **kwargs):
        auth_header = request.headers.get("Authorization")

        if not auth_header:
            return jsonify({"error": "No authorization header"}), 401

        try:
            # Extract token from "Bearer <token>"
            token = auth_header.split(" ")[1]
            payload = verify_token(token)

            if not payload:
                return jsonify({"error": "Invalid or expired token"}), 401

            # Add user info to request context
            request.user = payload
            return f(*args, **kwargs)

        except IndexError:
            return jsonify({"error": "Invalid authorization header format"}), 401

    return decorated_function


def validate_sparql_query(query: str) -> tuple[bool, str]:
    """
    Validate SPARQL query for safety and complexity
    Returns (is_valid, error_message)
    """
    # Remove comments and normalize whitespace
    cleaned_query = re.sub(r"#.*$", "", query, flags=re.MULTILINE)
    cleaned_query = " ".join(cleaned_query.split())

    # Basic validation - only allow SELECT queries
    if not cleaned_query.upper().startswith("SELECT"):
        return False, "Only SELECT queries are allowed"

    # Check for potentially dangerous keywords
    dangerous_keywords = [
        "INSERT",
        "DELETE",
        "DROP",
        "CREATE",
        "CLEAR",
        "LOAD",
        "COPY",
        "MOVE",
        "ADD",
        "REMOVE",
        "WITH",
    ]

    query_upper = cleaned_query.upper()
    for keyword in dangerous_keywords:
        if keyword in query_upper:
            return False, f"Dangerous keyword '{keyword}' not allowed"

    # Check query complexity
    complexity_score = calculate_query_complexity(cleaned_query)
    if complexity_score > 100:
        return False, "Query too complex (complexity score: {})".format(complexity_score)

    # Check for excessive number of variables
    variables = re.findall(r"\?[\w_]+", cleaned_query)
    if len(set(variables)) > 20:
        return False, "Too many variables in query (max 20)"

    # Check for excessive UNION or OPTIONAL clauses
    union_count = cleaned_query.upper().count("UNION")
    optional_count = cleaned_query.upper().count("OPTIONAL")

    if union_count > 5:
        return False, "Too many UNION clauses (max 5)"

    if optional_count > 10:
        return False, "Too many OPTIONAL clauses (max 10)"

    return True, ""


def calculate_query_complexity(query: str) -> int:
    """
    Calculate a complexity score for a SPARQL query
    Higher scores indicate more complex/expensive queries
    """
    score = 0

    # Base score for query length
    score += len(query) // 100

    # Score for triple patterns
    triple_patterns = query.count(".")
    score += triple_patterns * 2

    # Score for OPTIONAL patterns
    optional_count = query.upper().count("OPTIONAL")
    score += optional_count * 5

    # Score for UNION patterns
    union_count = query.upper().count("UNION")
    score += union_count * 10

    # Score for FILTER expressions
    filter_count = query.upper().count("FILTER")
    score += filter_count * 3

    # Score for property paths
    property_paths = len(re.findall(r"[+*]", query))
    score += property_paths * 15

    # Score for subqueries
    subquery_count = query.count("{")
    score += max(0, (subquery_count - 1) * 8)

    # Score for aggregation functions
    aggregations = ["COUNT", "SUM", "AVG", "MIN", "MAX", "GROUP BY", "HAVING"]
    for agg in aggregations:
        if agg in query.upper():
            score += 10

    return score


def validate_node_id(node_id: str) -> bool:
    """Validate that a node ID is safe and well-formed"""
    # Node IDs should only contain alphanumeric characters, hyphens, and underscores
    pattern = r"^[a-zA-Z0-9_-]+$"
    return bool(re.match(pattern, node_id))


def validate_search_term(term: str) -> bool:
    """Validate that a search term is safe"""
    # Limit length
    if len(term) > 100:
        return False

    # Check for potential injection attempts
    dangerous_chars = ["<", ">", '"', "'", "\\", "\0", "\n", "\r"]
    return not any(char in term for char in dangerous_chars)


def sanitize_output(data: Any) -> Any:
    """Sanitize output data to prevent XSS and other injection attacks"""
    if isinstance(data, str):
        # Basic HTML escaping
        return (
            data.replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace('"', "&quot;")
            .replace("'", "&#x27;")
        )
    elif isinstance(data, dict):
        return {k: sanitize_output(v) for k, v in data.items()}
    elif isinstance(data, list):
        return [sanitize_output(item) for item in data]
    else:
        return data

