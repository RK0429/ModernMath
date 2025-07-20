"""
Natural Language Query Interface for Math Knowledge Graph
Translates natural language questions into SPARQL queries
"""

import re
import json
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass
from SPARQLWrapper import SPARQLWrapper, JSON as SPARQL_JSON
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class QueryIntent:
    """Represents the intent of a natural language query"""

    query_type: str  # dependencies, dependents, examples, definition, path
    subject: Optional[str] = None
    target: Optional[str] = None
    domain: Optional[str] = None
    additional_params: Optional[Dict[str, Any]] = None


class NaturalLanguageQueryProcessor:
    """Processes natural language queries about mathematical concepts"""

    def __init__(self, sparql_endpoint: str = "http://localhost:3030/mathwiki/sparql"):
        self.sparql_endpoint = sparql_endpoint
        self.sparql = SPARQLWrapper(sparql_endpoint)
        self.sparql.setReturnFormat(SPARQL_JSON)

        # Define query patterns
        self.patterns = {
            "dependencies": [
                r"what (?:does|concepts does) (.+?) (?:depend on|use|require)",
                r"(?:show|list|find) (?:the )?dependencies (?:of|for) (.+)",
                r"what are the prerequisites (?:for|of) (.+)",
                r"(.+?) depends on what",
            ],
            "dependents": [
                r"what (?:depends on|uses|requires) (.+)",
                r"(?:show|list|find) (?:all )?(?:theorems|concepts) that "
                r"(?:use|depend on|require) (.+)",
                r"where is (.+?) used",
                r"(.+?) is used (?:by|in) what",
            ],
            "examples": [
                r"(?:show|list|find|give) (?:me )?examples? (?:of|for) (.+)",
                r"what are (?:some )?examples? (?:of|for) (.+)",
                r"(.+?) examples",
            ],
            "definition": [
                r"what is (?:the definition of )?(.+)",
                r"define (.+)",
                r"(?:show|explain) (.+)",
            ],
            "path": [
                r"(?:how|path) (?:to get )?from (.+?) to (.+)",
                r"(?:show|find) (?:the )?(?:path|connection) between (.+?) and (.+)",
                r"how (?:are|is) (.+?) (?:connected|related) to (.+)",
            ],
            "domain": [
                r"(?:show|list|find) (?:all )?(.+?) (?:concepts|definitions|theorems)",
                r"what (?:concepts|definitions|theorems) are in (.+)",
                r"(.+?) (?:concepts|definitions|theorems)",
            ],
        }

        # Common concept mappings
        self.concept_mappings = {
            "group": "def-group",
            "groups": "def-group",
            "set": "def-set",
            "sets": "def-set",
            "topological space": "def-topological-space",
            "vector space": "def-vector-space",
            "continuous": "def-continuity",
            "continuity": "def-continuity",
            "compact": "def-compact",
            "compactness": "def-compact",
            "limit": "def-limit",
            "limits": "def-limit",
            "derivative": "def-derivative",
            "derivatives": "def-derivative",
        }

        # Domain mappings
        self.domain_mappings = {
            "algebra": "Algebra",
            "topology": "Topology",
            "analysis": "Analysis",
            "geometry": "Geometry",
            "number theory": "Number Theory",
            "combinatorics": "Combinatorics",
            "category theory": "Category Theory",
            "probability": "Probability and Statistics",
            "logic": "Logic and Set Theory",
        }

    def parse_query(self, query: str) -> QueryIntent:
        """Parse natural language query to determine intent"""
        query_lower = query.lower().strip()

        # Try to match patterns
        for query_type, patterns in self.patterns.items():
            for pattern in patterns:
                match = re.search(pattern, query_lower)
                if match:
                    if query_type == "path":
                        # Extract both source and target
                        subject = self._normalize_concept(match.group(1))
                        target = self._normalize_concept(match.group(2))
                        return QueryIntent(query_type, subject=subject, target=target)
                    elif query_type == "domain":
                        # Extract domain
                        domain = self._normalize_domain(match.group(1))
                        return QueryIntent(query_type, domain=domain)
                    else:
                        # Extract subject
                        subject = self._normalize_concept(match.group(1))
                        return QueryIntent(query_type, subject=subject)

        # Default: try to interpret as definition query
        # Extract potential concept name
        concept_match = re.search(r"\b(\w+(?:\s+\w+)*)\b", query_lower)
        if concept_match:
            subject = self._normalize_concept(concept_match.group(1))
            return QueryIntent("definition", subject=subject)

        return QueryIntent("unknown")

    def _normalize_concept(self, concept: str) -> str:
        """Normalize concept name to match graph IDs"""
        concept = concept.strip().lower()

        # Check mappings
        if concept in self.concept_mappings:
            return self.concept_mappings[concept]

        # Try to construct ID
        # Remove common articles
        concept = re.sub(r"\b(the|a|an)\b", "", concept).strip()

        # Convert to ID format
        concept_id = concept.replace(" ", "-")

        # Add prefix if not present
        if not concept_id.startswith(("def-", "thm-", "ax-", "ex-")):
            # Try to guess type from context
            if any(word in concept for word in ["theorem", "lemma", "proposition"]):
                concept_id = "thm-" + concept_id.replace("theorem", "").strip()
            elif any(word in concept for word in ["example"]):
                concept_id = "ex-" + concept_id.replace("example", "").strip()
            elif any(word in concept for word in ["axiom"]):
                concept_id = "ax-" + concept_id.replace("axiom", "").strip()
            else:
                concept_id = "def-" + concept_id

        return concept_id

    def _normalize_domain(self, domain: str) -> str:
        """Normalize domain name"""
        domain = domain.strip().lower()
        return self.domain_mappings.get(domain, domain.title())

    def build_sparql_query(self, intent: QueryIntent) -> str:
        """Build SPARQL query from intent"""
        prefix = """
        PREFIX mymath: <https://mathwiki.org/ontology#>
        PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
        PREFIX base: <https://mathwiki.org/resource/>
        """

        if intent.query_type == "dependencies":
            return (
                prefix
                + f"""
            SELECT ?dep ?depLabel ?depType
            WHERE {{
                base:{intent.subject} mymath:uses ?dep .
                ?dep rdfs:label ?depLabel .
                ?dep rdf:type ?depType .
            }}
            ORDER BY ?depLabel
            """
            )

        elif intent.query_type == "dependents":
            return (
                prefix
                + f"""
            SELECT ?node ?nodeLabel ?nodeType
            WHERE {{
                ?node mymath:uses base:{intent.subject} .
                ?node rdfs:label ?nodeLabel .
                ?node rdf:type ?nodeType .
            }}
            ORDER BY ?nodeLabel
            """
            )

        elif intent.query_type == "examples":
            return (
                prefix
                + f"""
            SELECT ?example ?exampleLabel
            WHERE {{
                ?example mymath:isExampleOf base:{intent.subject} .
                ?example rdfs:label ?exampleLabel .
            }}
            ORDER BY ?exampleLabel
            """
            )

        elif intent.query_type == "definition":
            return (
                prefix
                + f"""
            SELECT ?label ?type ?domain
            WHERE {{
                base:{intent.subject} rdfs:label ?label .
                base:{intent.subject} rdf:type ?type .
                OPTIONAL {{ base:{intent.subject} mymath:hasDomain ?domain }}
            }}
            LIMIT 1
            """
            )

        elif intent.query_type == "path":
            # Simple path query (up to 3 hops)
            return (
                prefix
                + f"""
            SELECT ?path1 ?path2 ?path3
            WHERE {{
                {{
                    base:{intent.subject} mymath:uses* ?path1 .
                    ?path1 mymath:uses* base:{intent.target} .
                    BIND(?path1 as ?path2)
                    BIND(?path1 as ?path3)
                }}
                UNION
                {{
                    base:{intent.subject} mymath:uses* ?path1 .
                    ?path1 mymath:uses* ?path2 .
                    ?path2 mymath:uses* base:{intent.target} .
                    BIND(?path2 as ?path3)
                }}
                UNION
                {{
                    base:{intent.subject} mymath:uses* ?path1 .
                    ?path1 mymath:uses* ?path2 .
                    ?path2 mymath:uses* ?path3 .
                    ?path3 mymath:uses* base:{intent.target} .
                }}
            }}
            LIMIT 10
            """
            )

        elif intent.query_type == "domain":
            return (
                prefix
                + f"""
            SELECT ?node ?nodeLabel ?nodeType
            WHERE {{
                ?node mymath:hasDomain "{intent.domain}" .
                ?node rdfs:label ?nodeLabel .
                ?node rdf:type ?nodeType .
            }}
            ORDER BY ?nodeType ?nodeLabel
            """
            )

        else:
            # Unknown query type - return empty query
            return ""

    def execute_query(self, sparql_query: str) -> List[Dict[str, Any]]:
        """Execute SPARQL query and return results"""
        if not sparql_query:
            return []

        try:
            self.sparql.setQuery(sparql_query)
            results = self.sparql.query().convert()

            # Convert results to simpler format
            simplified_results = []
            for result in results["results"]["bindings"]:
                simplified = {}
                for key, value in result.items():
                    simplified[key] = value["value"]
                simplified_results.append(simplified)

            return simplified_results

        except Exception as e:
            logger.error(f"SPARQL query failed: {e}")
            return []

    def format_response(self, intent: QueryIntent, results: List[Dict[str, Any]]) -> str:
        """Format query results as natural language response"""
        if not results:
            return ("I couldn't find any information about that. "
                    "Please check if the concept exists in the knowledge graph.")

        if intent.query_type == "dependencies":
            deps = [r["depLabel"] for r in results]
            if deps:
                return f"{intent.subject} depends on: {', '.join(deps)}"
            else:
                return f"{intent.subject} has no recorded dependencies."

        elif intent.query_type == "dependents":
            deps = [r["nodeLabel"] for r in results]
            if deps:
                return f"The following concepts depend on {intent.subject}: {', '.join(deps)}"
            else:
                return f"No concepts currently depend on {intent.subject}."

        elif intent.query_type == "examples":
            examples = [r["exampleLabel"] for r in results]
            if examples:
                return f"Examples of {intent.subject}: {', '.join(examples)}"
            else:
                return f"No examples found for {intent.subject}."

        elif intent.query_type == "definition":
            result = results[0]
            type_name = result["type"].split("#")[-1]
            response = f"{result['label']} is a {type_name}."
            if "domain" in result:
                response += f" It belongs to {result['domain']}."
            return response

        elif intent.query_type == "path":
            if results:
                return f"Found {len(results)} paths from {intent.subject} to {intent.target}."
            else:
                return f"No connection found between {intent.subject} and {intent.target}."

        elif intent.query_type == "domain":
            by_type = {}
            for r in results:
                type_name = r["nodeType"].split("#")[-1]
                if type_name not in by_type:
                    by_type[type_name] = []
                by_type[type_name].append(r["nodeLabel"])

            parts = []
            for type_name, items in by_type.items():
                parts.append(f"{len(items)} {type_name}s")

            return f"{intent.domain} contains: {', '.join(parts)}"

        return "I processed your query but couldn't format the results properly."

    def answer_question(self, question: str) -> Tuple[str, Dict[str, Any]]:
        """Main method to answer a natural language question"""
        # Parse the question
        intent = self.parse_query(question)

        # Build SPARQL query
        sparql_query = self.build_sparql_query(intent)

        # Execute query
        results = self.execute_query(sparql_query)

        # Format response
        response = self.format_response(intent, results)

        # Return response and metadata
        metadata = {
            "intent": {
                "type": intent.query_type,
                "subject": intent.subject,
                "target": intent.target,
                "domain": intent.domain,
            },
            "sparql_query": sparql_query,
            "result_count": len(results),
        }

        return response, metadata


# CLI interface
if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Natural Language Query Interface")
    parser.add_argument("question", nargs="?", help="Question to ask")
    parser.add_argument(
        "--endpoint",
        "-e",
        default="http://localhost:3030/mathwiki/sparql",
        help="SPARQL endpoint URL",
    )
    parser.add_argument("--interactive", "-i", action="store_true", help="Run in interactive mode")
    parser.add_argument("--debug", "-d", action="store_true", help="Show debug information")

    args = parser.parse_args()

    # Initialize processor
    processor = NaturalLanguageQueryProcessor(args.endpoint)

    if args.interactive:
        print("Math Knowledge Graph Query Interface")
        print("Type 'quit' or 'exit' to stop")
        print("-" * 40)

        while True:
            try:
                question = input("\nAsk a question: ").strip()
                if question.lower() in ["quit", "exit"]:
                    break

                if not question:
                    continue

                response, metadata = processor.answer_question(question)
                print(f"\n{response}")

                if args.debug:
                    print("\nDebug info:")
                    print(json.dumps(metadata, indent=2))

            except KeyboardInterrupt:
                print("\nGoodbye!")
                break
            except Exception as e:
                print(f"Error: {e}")

    elif args.question:
        response, metadata = processor.answer_question(args.question)
        print(response)

        if args.debug:
            print("\nDebug info:")
            print(json.dumps(metadata, indent=2))

    else:
        parser.print_help()

