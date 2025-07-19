#!/usr/bin/env python3
"""
Query interface for the Math Knowledge Graph via SPARQL endpoint
"""

import argparse
from SPARQLWrapper import SPARQLWrapper, JSON
from typing import Dict, List, Any
import json


class MathKnowledgeGraphQuery:
    """Interface for querying the Math Knowledge Graph"""
    
    def __init__(self, endpoint: str = "http://localhost:3030/mathwiki/sparql"):
        self.endpoint = endpoint
        self.sparql = SPARQLWrapper(endpoint)
        self.sparql.setReturnFormat(JSON)
        
        # Define prefixes
        self.prefixes = """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX base: <https://mathwiki.org/resource/>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        """
    
    def execute_query(self, query: str) -> List[Dict[str, Any]]:
        """Execute a SPARQL query and return results"""
        full_query = self.prefixes + query
        self.sparql.setQuery(full_query)
        
        try:
            results = self.sparql.query().convert()
            if "results" in results and "bindings" in results["results"]:
                return results["results"]["bindings"]
            return []
        except Exception as e:
            print(f"Error executing query: {e}")
            return []
    
    def get_node_info(self, node_id: str) -> Dict[str, Any]:
        """Get information about a specific node"""
        query = f"""
        SELECT ?type ?label ?status ?domain
        WHERE {{
            base:{node_id} a ?type .
            OPTIONAL {{ base:{node_id} rdfs:label ?label }}
            OPTIONAL {{ base:{node_id} mymath:hasStatus ?status }}
            OPTIONAL {{ base:{node_id} mymath:hasDomain ?domain }}
        }}
        """
        results = self.execute_query(query)
        if results:
            return results[0]
        return {}
    
    def get_dependencies(self, node_id: str) -> List[Dict[str, str]]:
        """Get all dependencies of a node"""
        query = f"""
        SELECT ?dep ?label ?type
        WHERE {{
            base:{node_id} mymath:uses ?dep .
            OPTIONAL {{ ?dep rdfs:label ?label }}
            OPTIONAL {{ ?dep a ?type }}
        }}
        ORDER BY ?label
        """
        return self.execute_query(query)
    
    def get_dependents(self, node_id: str) -> List[Dict[str, str]]:
        """Get all nodes that depend on this node"""
        query = f"""
        SELECT ?dependent ?label ?type
        WHERE {{
            ?dependent mymath:uses base:{node_id} .
            OPTIONAL {{ ?dependent rdfs:label ?label }}
            OPTIONAL {{ ?dependent a ?type }}
        }}
        ORDER BY ?label
        """
        return self.execute_query(query)
    
    def find_by_type(self, node_type: str) -> List[Dict[str, str]]:
        """Find all nodes of a specific type"""
        query = f"""
        SELECT ?node ?label ?domain
        WHERE {{
            ?node a mymath:{node_type} .
            OPTIONAL {{ ?node rdfs:label ?label }}
            OPTIONAL {{ ?node mymath:hasDomain ?domain }}
        }}
        ORDER BY ?domain ?label
        """
        return self.execute_query(query)
    
    def find_by_domain(self, domain: str) -> List[Dict[str, str]]:
        """Find all nodes in a specific mathematical domain"""
        query = f"""
        SELECT ?node ?label ?type
        WHERE {{
            ?node mymath:hasDomain "{domain}" .
            ?node a ?type .
            OPTIONAL {{ ?node rdfs:label ?label }}
        }}
        ORDER BY ?type ?label
        """
        return self.execute_query(query)
    
    def get_graph_stats(self) -> Dict[str, int]:
        """Get statistics about the knowledge graph"""
        stats = {}
        
        # Count total nodes
        query = "SELECT (COUNT(DISTINCT ?s) as ?count) WHERE { ?s ?p ?o }"
        results = self.execute_query(query)
        if results:
            stats['total_nodes'] = int(results[0]['count']['value'])
        
        # Count by type
        for node_type in ['Definition', 'Theorem', 'Example', 'Axiom']:
            query = f"""
            SELECT (COUNT(DISTINCT ?node) as ?count)
            WHERE {{ ?node a mymath:{node_type} }}
            """
            results = self.execute_query(query)
            if results:
                stats[f'{node_type.lower()}s'] = int(results[0]['count']['value'])
        
        # Count relationships
        query = """
        SELECT (COUNT(*) as ?count)
        WHERE { ?s mymath:uses ?o }
        """
        results = self.execute_query(query)
        if results:
            stats['relationships'] = int(results[0]['count']['value'])
        
        return stats


def format_results(results: List[Dict[str, Any]]) -> None:
    """Pretty print query results"""
    if not results:
        print("No results found.")
        return
    
    for i, result in enumerate(results):
        print(f"\n{i+1}. ", end="")
        items = []
        for key, value in result.items():
            val = value['value']
            # Extract local name from URI
            if value['type'] == 'uri':
                if '#' in val:
                    val = val.split('#')[-1]
                elif '/' in val:
                    val = val.split('/')[-1]
            items.append(f"{key}: {val}")
        print(", ".join(items))


def main():
    parser = argparse.ArgumentParser(description='Query the Math Knowledge Graph')
    parser.add_argument('--endpoint', default='http://localhost:3030/mathwiki/sparql',
                        help='SPARQL endpoint URL')
    
    subparsers = parser.add_subparsers(dest='command', help='Commands')
    
    # Info command
    info_parser = subparsers.add_parser('info', help='Get information about a node')
    info_parser.add_argument('node_id', help='Node ID (e.g., def-group)')
    
    # Dependencies command
    deps_parser = subparsers.add_parser('deps', help='Get dependencies of a node')
    deps_parser.add_argument('node_id', help='Node ID')
    
    # Dependents command
    dependents_parser = subparsers.add_parser('dependents', help='Get nodes that depend on this node')
    dependents_parser.add_argument('node_id', help='Node ID')
    
    # Find by type command
    type_parser = subparsers.add_parser('find-type', help='Find nodes by type')
    type_parser.add_argument('type', choices=['Definition', 'Theorem', 'Example', 'Axiom'],
                           help='Node type')
    
    # Find by domain command
    domain_parser = subparsers.add_parser('find-domain', help='Find nodes by domain')
    domain_parser.add_argument('domain', help='Mathematical domain (e.g., Algebra)')
    
    # Stats command
    stats_parser = subparsers.add_parser('stats', help='Get graph statistics')
    
    # Custom query command
    query_parser = subparsers.add_parser('query', help='Execute custom SPARQL query')
    query_parser.add_argument('sparql', help='SPARQL query (without prefixes)')
    
    args = parser.parse_args()
    
    # Create query interface
    kg = MathKnowledgeGraphQuery(args.endpoint)
    
    # Execute command
    if args.command == 'info':
        info = kg.get_node_info(args.node_id)
        if info:
            print(f"\nInformation for {args.node_id}:")
            format_results([info])
        else:
            print(f"Node {args.node_id} not found.")
    
    elif args.command == 'deps':
        deps = kg.get_dependencies(args.node_id)
        print(f"\nDependencies of {args.node_id}:")
        format_results(deps)
    
    elif args.command == 'dependents':
        deps = kg.get_dependents(args.node_id)
        print(f"\nNodes that depend on {args.node_id}:")
        format_results(deps)
    
    elif args.command == 'find-type':
        nodes = kg.find_by_type(args.type)
        print(f"\nAll {args.type}s:")
        format_results(nodes)
    
    elif args.command == 'find-domain':
        nodes = kg.find_by_domain(args.domain)
        print(f"\nNodes in {args.domain}:")
        format_results(nodes)
    
    elif args.command == 'stats':
        stats = kg.get_graph_stats()
        print("\nKnowledge Graph Statistics:")
        print(json.dumps(stats, indent=2))
    
    elif args.command == 'query':
        results = kg.execute_query(args.sparql)
        print("\nQuery Results:")
        format_results(results)
    
    else:
        parser.print_help()


if __name__ == "__main__":
    main()