"""
Test script for the Math Knowledge Graph REST API
"""

import requests
import json

BASE_URL = "http://localhost:5000/api"


def print_response(response: requests.Response, title: str):
    """Pretty print API response"""
    print(f"\n{'='*50}")
    print(f"{title}")
    print(f"{'='*50}")
    print(f"Status Code: {response.status_code}")
    try:
        data = response.json()
        print(json.dumps(data, indent=2))
    except json.JSONDecodeError:
        print(response.text)


def test_health_check():
    """Test the health check endpoint"""
    response = requests.get(f"{BASE_URL}/health")
    print_response(response, "Health Check")
    return response.status_code == 200


def test_get_node(node_id: str = "def-group"):
    """Test getting a specific node"""
    response = requests.get(f"{BASE_URL}/nodes/{node_id}")
    print_response(response, f"Get Node: {node_id}")
    return response.status_code == 200


def test_get_dependencies(node_id: str = "thm-unique-identity"):
    """Test getting dependencies of a node"""
    response = requests.get(f"{BASE_URL}/dependencies/{node_id}")
    print_response(response, f"Dependencies of: {node_id}")
    return response.status_code == 200


def test_get_dependents(node_id: str = "def-group"):
    """Test getting dependents of a node"""
    response = requests.get(f"{BASE_URL}/dependents/{node_id}")
    print_response(response, f"Nodes that depend on: {node_id}")
    return response.status_code == 200


def test_search(search_term: str = "group"):
    """Test search functionality"""
    response = requests.get(f"{BASE_URL}/search", params={"q": search_term})
    print_response(response, f"Search for: {search_term}")
    return response.status_code == 200


def test_get_all_nodes():
    """Test getting all nodes"""
    response = requests.get(f"{BASE_URL}/nodes")
    print_response(response, "All Nodes (truncated)")
    # Truncate output for readability
    if response.status_code == 200:
        data = response.json()
        if "results" in data and len(data["results"]) > 5:
            print(f"... showing first 5 of {data['count']} nodes")
            data["results"] = data["results"][:5]
            print(json.dumps(data, indent=2))
    return response.status_code == 200


def test_custom_query():
    """Test custom SPARQL query"""
    query = """
    PREFIX mymath: <https://mathwiki.org/ontology#>
    PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
    
    SELECT ?theorem ?label
    WHERE {
        ?theorem a mymath:Theorem ;
                rdfs:label ?label .
    }
    LIMIT 5
    """

    response = requests.post(
        f"{BASE_URL}/query", json={"query": query}, headers={"Content-Type": "application/json"}
    )
    print_response(response, "Custom Query: Get 5 Theorems")
    return response.status_code == 200


def run_all_tests():
    """Run all API tests"""
    print("Math Knowledge Graph API Test Suite")
    print("Make sure the API server is running on http://localhost:5000")
    print("And Fuseki is running on http://localhost:3030")

    tests = [
        ("Health Check", test_health_check),
        ("Get Node", test_get_node),
        ("Get Dependencies", test_get_dependencies),
        ("Get Dependents", test_get_dependents),
        ("Search Nodes", test_search),
        ("Get All Nodes", test_get_all_nodes),
        ("Custom Query", test_custom_query),
    ]

    results = []
    for test_name, test_func in tests:
        try:
            success = test_func()
            results.append((test_name, "PASS" if success else "FAIL"))
        except Exception as e:
            print(f"\nError in {test_name}: {str(e)}")
            results.append((test_name, "ERROR"))

    print("\n" + "=" * 50)
    print("TEST SUMMARY")
    print("=" * 50)
    for test_name, result in results:
        print(f"{test_name}: {result}")


if __name__ == "__main__":
    run_all_tests()
