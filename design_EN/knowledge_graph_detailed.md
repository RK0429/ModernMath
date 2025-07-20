# **Building a Full-Scale Mathematical Knowledge Graph from Scratch**

## **I. Introduction: A Principled Framework for a Semantic Mathematical Wiki**

### **A. Project Vision and Goals**

The goal of building an evolving, queryable wiki covering all fields of mathematics as a knowledge graph represents a paradigm shift in the structuring and accessibility of mathematical knowledge. At its core, the aim is to represent axioms, definitions, theorems, and examples as interconnected nodes, creating a system where users (and machines) can query relationships, such as "What theorems depend on this axiom?", and discover new connections [1]. This vision is not merely a document repository but aims to construct a "semantic wiki" or a "searchable database of mathematical results" that reflects the logical structure of mathematics itself.

To achieve this ambitious goal, this report proposes a "build from scratch" approach. Advanced projects like MaRDI (Mathematical Research Data Initiative) have constructed comprehensive knowledge graphs linking millions of mathematical items on the Wikibase platform (a customized Wikipedia) [2]. While this approach excels in leveraging a powerful existing platform [5], the from-scratch approach detailed in this report offers the invaluable advantage of complete control over the technology stack, data model, and final user experience, enabling a system optimized for the project's specific requirements.

### **B. Philosophy of an Integrated Architecture**

The proposed architecture is designed around a virtuous cycle of four phases:

1. **Authoring (Quarto):** Humans create structured, readable content.
2. **Extraction (Python):** Automated scripts parse this content and transform it into a formal graph structure.
3. **Querying (SPARQL/API):** The generated graph is published for exploration and analysis.
4. **Enrichment (Visualization & LLM):** Insights from the graph are fed back into the authoring environment and power intelligent assistant features.

This architecture is designed from the outset to ensure scalability, maintainability, and extensibility, serving as the foundation for a long-term project that will gradually encompass the vast domain of mathematics.

### **C. Structure and Roadmap of this Report**

This report is structured as a concrete blueprint for realizing this vision. We begin with the design of the ontology, the logical foundation of the knowledge graph. Next, we detail efficient content creation methods using Quarto and specifically show how to convert it into formal graph data with a Python-based pipeline. Furthermore, we discuss ensuring rigor through integration with the Lean 4 proof assistant, publishing and querying data via a SPARQL endpoint, and realizing an interactive exploration experience through graph visualization. Finally, we present a strategy for ensuring automation and scalability using CI/CD pipelines and Large Language Models (LLMs), concluding with the project's overall integration and a phased implementation plan.

## **II. Foundational Design: Constructing a Mathematical Ontology**

### **A. The Central Role of Ontology**

The first and most crucial step in building a knowledge graph is to define its "schema," the ontology. An ontology formally defines the types of "things" (classes) that exist in the graph and the types of "relationships" (properties) between them [1]. This is the cornerstone of the entire system's design philosophy, ensuring data consistency and enabling logical inference. The fact that major mathematical knowledge projects like OntoMathPRO [6] and MaRDI [8] have built elaborate ontologies as their foundation speaks to the importance of this step.

### **B. Core Node and Relationship Types**

For the mathematical knowledge domain, we define the following primary nodes (classes) and relationships (properties):

* **Node Types (Classes):**
  * Axiom
  * Definition
  * Theorem: Includes Lemma, Proposition, Corollary.
  * Example
* **Relationship Types (Properties):**
  * uses / dependsOn: The most critical relationship, forming the dependency graph (e.g., a theorem *uses* a definition).
  * hasExample / isExampleOf: Connects concepts with concrete instances.
  * generalizes / specializes: Captures hierarchical relationships between concepts.
  * implies: Indicates a more specific logical implication inherent in a theorem.

### **C. Architectural Decision: RDF vs. Property Graph**

The project requirement to "publish data as Linked Data" is a decisive factor in technology selection. To meet this requirement most faithfully and directly, an RDF (Resource Description Framework) native approach is optimal.

Linked Data is based on W3C standard technologies: URIs, HTTP, and RDF [10].

Libraries like `rdflib` and triple stores like Apache Jena Fuseki are tools designed precisely for this purpose [12]. On the other hand, property graphs like Neo4j, adopted by the Lean knowledge graph project, are very powerful but not RDF-native [14]. The property graph model (with key-value properties on both nodes and edges) is fundamentally different from RDF's triple (subject-predicate-object) model [15].

While bridges like `rdflib-neo4j` [16] exist, they introduce an additional translation layer and carry the risk of impedance mismatch.

Therefore, to achieve the primary goal of Linked Data publication with the highest fidelity and minimal complexity, adopting RDF as the core data model is the logical conclusion. This project will take an RDF-first strategy, and the knowledge graph should be natively represented as a collection of RDF triples.

**Table 1: Comparison of Knowledge Graph Models (RDF vs. Property Graph)**

| Evaluation Criterion | RDF (Resource Description Framework) | Property Graph (e.g., Neo4j) |
| :--- | :--- | :--- |
| **W3C Standard** | ✓ (RDF, RDFS, OWL, SPARQL) | ✗ (GQL is undergoing ISO standardization) |
| **Linked Data Native Support** | ✓ (Core design philosophy) | △ (Requires translation layer) |
| **Query Language** | SPARQL | Cypher, GQL |
| **Schema** | Formal definition with RDFS/OWL | Implicit or constraint-based definition |
| **Tool Ecosystem** | Mature in academic, open data fields | Mature in enterprise, analytics fields |
| **Data Model** | Subject-Predicate-Object triples | Nodes and relationships with properties |

### **D. Formalizing the Ontology with RDF/OWL**

The plan for creating a concrete ontology file (e.g., `math-ontology.ttl`) is as follows. First, we define a custom namespace (e.g., `PREFIX mymath: <https://mathwiki.org/ontology#`). Next, we use OWL/RDFS to define the core classes and properties.

Code Snippet

```turtle
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
@prefix owl: <http://www.w3.org/2002/07/owl#>.
@prefix skos: <http://www.w3.org/2004/02/skos/core#>.
@prefix mymath: <https://mathwiki.org/ontology#>.

mymath:Theorem a rdfs:Class ;
    rdfs:subClassOf skos:Concept ;
    rdfs:label "Theorem"@en ;
    rdfs:comment "A mathematical statement that has been proved on the basis of previously established statements, such as other theorems, and generally accepted statements, such as axioms."@en.

mymath:Definition a rdfs:Class ;
    rdfs:subClassOf skos:Concept ;
    rdfs:label "Definition"@en.

mymath:uses a rdf:Property ;
    rdfs:domain mymath:Theorem ;
    rdfs:range skos:Concept ;
    rdfs:label "uses"@en ;
    rdfs:comment "Indicates that the subject (e.g., a theorem) depends on or utilizes the object (e.g., a definition or another theorem) in its proof or statement."@en.
```

Furthermore, to avoid reinventing the wheel and dramatically improve interoperability, it is essential to map our custom ontology to existing, established ontologies. Projects like OntoMathPRO [6] and OMV (Ontology Metadata Vocabulary) [17] have conducted extensive research on modeling mathematical knowledge. By linking to the classes and properties of these external schemas using `owl:equivalentClass` or `rdfs:subClassOf`, our graph gains semantic context within the broader Linked Open Data cloud from the moment of its creation. This provides immeasurable benefits for machine readability and integration with external systems.

**Table 2: Schema of the Core Mathematical Ontology**

| Label | Type | URI | RDFS Comment | External Mapping (Example) |
| :--- | :--- | :--- | :--- | :--- |
| Theorem | Class | mymath:Theorem | A proven mathematical statement | `owl:equivalentClass ontomathpro:Theorem` |
| Definition | Class | mymath:Definition | A statement defining the meaning of a concept | `owl:equivalentClass ontomathpro:Definition` |
| Axiom | Class | mymath:Axiom | A statement taken as true without proof | `owl:equivalentClass ontomathpro:Axiom` |
| Example | Class | mymath:Example | A concrete illustration of a concept or theorem | `rdfs:subClassOf skos:Concept` |
| uses | Property | mymath:uses | The subject utilizes the object in a proof or definition | `rdfs:subPropertyOf skos:related` |
| hasExample | Property | mymath:hasExample | The subject has the object as an example | `rdfs:subPropertyOf skos:related` |

## **III. Authoring Environment: Weaving the Graph with Quarto**

### **A. Guiding Principle: Human Curation of Edges**

The reliability of the knowledge graph hinges on disciplined authoring. The primary mechanism for generating the graph's edges (relationships) is explicit, manual link creation by authors. This human curation is the foundation of a high-quality graph.

### **B. File and Directory Structure**

We recommend a "one concept, one file" policy. For example, `definitions/def-group.qmd`, `theorems/thm-group-isomorphism.qmd`, giving each mathematical object its own file. This structure, by leveraging Quarto's project-level metadata features, leads to further automation and consistency.

In a Quarto project, placing a `_metadata.yml` file within a subdirectory applies common metadata to all documents in that directory [19]. We will use this feature to organize content by mathematical field (e.g., `/algebra`, `/topology`). By placing a `_metadata.yml` file with the content `domain: "Algebra"` in the `/algebra` directory, the parsing script described later can read this metadata and automatically add a triple like `mymath:def-group mymath:hasDomain "Algebra"` for all nodes in that directory. This creates an automation layer that reduces the author's burden and ensures classification consistency.

### **C. Mastering Quarto Cross-References**

We will thoroughly utilize Quarto's cross-reference functionality for creating and referencing each node. Every theorem, definition, etc., must be given a unique label (e.g., `{#def-group}`) [20]. The core authoring rule is as follows:

**"When referencing another concept, always use the `@` syntax (e.g., `@def-group`)."**

By adhering to this convention, a clear pipeline is established where Quarto generates standard hyperlinks in the HTML output, and these links are interpreted as graph edges by the backend parser.

### **D. Embedding Machine-Readable Metadata in YAML Front Matter**

Quarto interprets some keys in the YAML front matter at the top of a `.qmd` file but ignores other custom keys [21]. We will leverage this property to embed our own metadata necessary for graph construction in each file.

Libraries like `python-frontmatter` [23] can easily extract this custom metadata.

We propose that each `.qmd` file's YAML header include the following standard set of keys:

**Table 3: Quarto Node Metadata Specification**

| Key | Type | Description |
| :--- | :--- | :--- |
| title | String | The human-readable title of the node (e.g., "Definition: Group"). |
| id | String | A unique, stable identifier for the node. Should match the cross-reference label (e.g., `def-group`). |
| type | String | The node's type in the ontology (e.g., Definition, Theorem). Essential for the parser. |
| status | String | The maturity of the content (e.g., stub, draft, complete, verified). |
| lean_id | String | (Optional) The identifier of the corresponding formal proof in the Lean library. Used for integration with the formal verification layer. |
| requires | Array | (Optional) An explicit list of dependency IDs. Complements links in the body and is useful for implicit dependencies like axioms. |

Below is an example of a complete `.qmd` file header:

YAML

```yaml
---
title: "Definition: Group"
id: "def-group"
type: "Definition"
status: "complete"
lean_id: "Mathlib.GroupTheory.Group.group"
requires:
  - "def-set"
  - "def-binary-operation"
---

A group is a set equipped with a binary operation that combines any two elements to form a third element in such a way that four conditions called group axioms are satisfied, namely closure, associativity, identity and invertibility.
...
```

## **IV. Backend Pipeline: From Quarto Documents to a Queryable Graph**

### **A. Pipeline Architecture Overview**

The backend processing pipeline consists of the following steps:

1. Scan for `.qmd` files within the project.
2. For each file, parse the YAML front matter and Markdown content.
3. Extract node information (ID, type, title, etc.) and relationships (`@` links and `requires` list).
4. Construct RDF triples based on the extracted information.
5. Serialize the entire constructed graph into a standard graph format (e.g., Turtle).

### **B. Parsing Strategy: Raw Markdown vs. Rendered HTML**

There are two main approaches to extracting the graph structure from the content:

* **Approach 1 (Recommended): Parsing Raw `.qmd` Files**
  * **Tools:** Use the Python library `python-frontmatter` [23] to easily separate YAML metadata and Markdown content.
  * **Advantages:** It's fast because it avoids a full Quarto render. It provides direct access to the "source of truth" like metadata and `@label` links.
  * **Disadvantages:** Requires a robust regular expression or an AST (Abstract Syntax Tree) parser to find all `@label` references in the Markdown body.
* **Approach 2: Parsing Rendered HTML**
  * **Tools:** Use Python's `BeautifulSoup` library, as seen in the Lean knowledge graph project [14].
  * **Advantages:** Simplifies link extraction because Quarto resolves all cross-references into standard `<a>` tags with `href` attributes.
  * **Disadvantages:** Slower because it requires running `quarto render`. Also, parsing HTML can be more brittle to changes than parsing Markdown.

**Recommendation:** We recommend starting with parsing raw `.qmd` files for speed and directness. The `python-frontmatter` library is ideal for handling metadata, and extracting `@label`s is sufficiently manageable with a targeted regular expression.

### **C. Building the Graph with `rdflib`**

Here is the skeleton of the process for building the graph using Python and the `rdflib` library:

Python

```python
import frontmatter
import re
from pathlib import Path
from rdflib import Graph, Literal, Namespace, RDF, RDFS

# Define namespaces
MYMATH = Namespace("<https://mathwiki.org/ontology#>")
BASE_URI = "<https://mathwiki.org/resource/>"

# Initialize graph
g = Graph()
g.bind("mymath", MYMATH)
g.bind("rdfs", RDFS)

# Regex to extract cross-references
crossref_pattern = re.compile(r'@([a-zA-Z0-9_-]+)')

# Scan and process qmd files
for qmd_path in Path("content/").rglob("*.qmd"):
    with open(qmd_path, 'r', encoding='utf-8') as f:
        post = frontmatter.load(f)
        metadata = post.metadata
        content = post.content

    if 'id' not in metadata or 'type' not in metadata:
        continue # Skip files without required metadata

    node_id = metadata['id']
    node_uri = Namespace(BASE_URI)[node_id]

    # 1. Add triples for node type and label
    g.add((node_uri, RDF.type, MYMATH[metadata['type']]))
    if 'title' in metadata:
        g.add((node_uri, RDFS.label, Literal(metadata['title'], lang='en')))

    # 2. Extract dependencies from @-links in the body
    dependencies = set(crossref_pattern.findall(content))

    # 3. Add dependencies from YAML 'requires'
    if 'requires' in metadata and isinstance(metadata['requires'], list):
        dependencies.update(metadata['requires'])

    # 4. Add dependency triples
    for dep_id in dependencies:
        dep_uri = Namespace(BASE_URI)[dep_id]
        g.add((node_uri, MYMATH.uses, dep_uri))

# Serialize the graph
g.serialize(destination='knowledge_graph.ttl', format='turtle')

print("Knowledge graph generated successfully.")
```

### **D. Data Serialization and Storage**

In the final step of the script above, the entire constructed graph is output to a Turtle (`.ttl`) format file using `g.serialize()`. This `knowledge_graph.ttl` file becomes the primary artifact of the backend pipeline, ready for the next phase of publication or loading into a triple store.

## **V. Formal Verification and Rigor: Integrating the Lean 4 Ecosystem**

### **A. The Dependency Graph as "Ground Truth"**

Proof assistants like Lean possess a 100% accurate internal dependency graph. This is because when proving a new theorem, the compiler must know exactly which lemmas were used [25]. This formally verified dependency is an invaluable, high-fidelity data source for our knowledge graph.

### **B. Extracting Data from a Lean Repository**

**LeanDojo** is recommended as the primary tool for this task [27]. As shown in the LeanDojo documentation, running the `trace` command on a Lean project like `mathlib` can extract detailed dependency data. The most important output files are `*.dep_paths`, which show file-level dependencies, and `*.trace.xml`, which contains more detailed tactic and theorem-level information. These become the raw data for constructing the formal knowledge graph.

### **C. Bridging the Formal and Informal Graphs**

The key to connecting these two worlds (the human-written Quarto graph and the Lean-generated formal graph) is the `lean_id` field proposed in the Quarto YAML metadata mentioned earlier.

This bridge enables the following verification and enrichment workflow. First, we prepare a secondary Python script that parses both the Quarto graph and the LeanDojo output. When this script finds a `lean_id` (e.g., `Mathlib.Data.Real.Basic.mul_comm`) in a Quarto theorem node, it uses it as a key to search the Lean dependency graph. It then compares the dependencies recorded in Lean's graph with the `mymath:uses` relationships in the Quarto graph.

### **D. Verification and Enrichment Workflow**

This comparison process enables advanced validation like the following:

1. **Inconsistency Detection:** If a dependency used in the Lean proof is not linked in the Quarto text (or vice versa), the script flags this as an "inconsistency" and prompts for human review. This allows for the systematic discovery of logical flaws or omissions in the documentation.
2. **Adding Verified Triples:** If the dependencies match, the script adds a new triple, `mymath:isVerifiedBy`, to the Quarto graph. This triple links the Quarto theorem node to a new node representing the formal Lean proof. This forms a "formally verified" subgraph within the graph, significantly increasing the reliability of the knowledge.

Through this workflow, human-created knowledge and machine-verified knowledge merge, elevating the knowledge graph from a mere collection of information to a reliable logical system.

## **VI. Publication and Querying: Exposing Knowledge as Linked Data**

### **A. Deploying a SPARQL Endpoint with Apache Jena Fuseki**

To make the constructed knowledge graph available to applications and users worldwide, we will publish a SPARQL endpoint. Apache Jena Fuseki is a robust, standard triple store server for this purpose. Based on the Fuseki quickstart guide, we set it up with the following steps [13]:

1. Download and launch the Fuseki server.
2. Access the web-based admin UI (usually at `http://localhost:3030/`) and create a new dataset (in-memory or persistent TDB).
3. Upload the `knowledge_graph.ttl` file generated by the backend pipeline to the created dataset.

This makes a dedicated SPARQL query UI available for each dataset, ready for live queries against the graph.

### **B. Enabling Live Queries**

The SPARQL endpoint provides a standard interface for querying the graph via HTTP. This allows us to answer various questions in line with the project's goals.

* **Example 1: Find all theorems that depend on the Axiom of Choice**
    Code Snippet

    ```sparql
    PREFIX mymath: <https://mathwiki.org/ontology#>
    PREFIX base: <https://mathwiki.org/resource/>

    SELECT ?theorem_label
    WHERE {
      ?theorem mymath:uses+ base:axiom-of-choice .
      ?theorem rdfs:label ?theorem_label .
    }
    ```

* **Example 2: Find the complete dependency chain for a specific theorem (transitive query)**
    Code Snippet

    ```sparql
    PREFIX mymath: <https://mathwiki.org/ontology#>
    PREFIX base: <https://mathwiki.org/resource/>

    SELECT DISTINCT ?dependency_label
    WHERE {
      base:thm-pythagorean mymath:uses+ ?dependency .
      ?dependency rdfs:label ?dependency_label .
    }
    ```

    (`uses+` means one or more `uses` relationships in a chain)

### **C. Creating a User-Friendly Query API (Optional but Recommended)**

While SPARQL is powerful, it can be too complex for many end-users. To encourage broader use, building a simple API wrapper on top of the SPARQL endpoint is effective.

* **REST API:** Using a Python framework (Flask or FastAPI), create intuitive endpoints like `/api/dependencies?id=thm-pythagorean` [29]. This endpoint would internally execute a predefined SPARQL query and return the results as formatted JSON.
* **GraphQL API:** For more complex client-side requirements, GraphQL is suitable. GraphQL is a strongly-typed query language that allows clients to specify exactly the data they need. Using `neo4j-graphql` [31] (if using Neo4j) or a generic GraphQL-to-SPARQL library, the ontology can be exposed as a GraphQL schema. This significantly simplifies data access, especially for frontend developers.

## **VII. Interactive Exploration: Visualizing the Knowledge Graph**

### **A. Closing the Knowledge Loop**

The true value of a knowledge graph is realized when users can intuitively understand and explore its structure. By embedding concrete visuals of the abstract graph structure into Quarto pages, we close this "knowledge loop" and promote serendipitous discovery.

### **B. Static and Simple Visualization with Mermaid**

Quarto natively supports Mermaid, a text-based diagramming tool [20]. We can use this to visually represent the context of each node page. As part of the CI/CD pipeline, for each node (e.g., `def-group`), we can execute a SPARQL query to retrieve all nodes one hop away (dependencies and dependents). Then, from the results, we can automatically generate Mermaid's `graph TD` syntax and insert it into the corresponding `.qmd` file before rendering. This allows for easily embedding a static dependency diagram on each page, showing the concept's position within the overall structure.

### **C. Dynamic and Interactive Visualization**

For a richer exploration experience, an interactive graph that users can manipulate is ideal. Thanks to Quarto's support for Observable JS (OJS) and htmlwidgets, this can be achieved without complex server-side rendering [33].

The key to this approach is client-side processing. Quarto can execute JavaScript in `{ojs}` code blocks directly in the user's browser [34]. Libraries like D3.js [35] and Vis.js are standard tools for web-based graph visualization.

The specific implementation strategy is as follows:

1. **Data Generation:** In the backend or CI/CD pipeline, generate a small JSON file (e.g., `def-group.json`) corresponding to each node page (e.g., `def-group.qmd`). This JSON file contains the data for the node's local graph neighborhood (e.g., nodes and edges within 2 hops).
2. **Visualization Component Creation:** Create a reusable OJS code chunk. This chunk will `require` the D3.js library, asynchronously load the corresponding JSON file for the page, and render it as an interactive force-directed layout graph.
3. **Embedding:** Include this OJS chunk in the Quarto pages where you want to display the relevant information.

This method makes the visualization logic reusable and efficient, as data loading is done only for what's needed on each page. Also, for developers primarily using R or Python, libraries like `pyvis` (Python) or `visNetwork` (R) can generate self-contained interactive HTML widgets, which Quarto can also embed directly from a code chunk [36].

## **VIII. Automation and Scalability: CI/CD Pipelines and LLM-Assisted Curation**

### **A. The CI/CD Pipeline as the System's Backbone**

To manage and maintain a project of this scale, thorough automation is essential. We will build a robust continuous integration/continuous deployment (CI/CD) pipeline using GitHub Actions and the official Quarto action [37]. This pipeline will be the backbone that ensures the quality and consistency of the entire system.

**Table 4: CI/CD Pipeline Stages and Actions**

| Stage | Action | Description |
| :--- | :--- | :--- |
| **1. Setup** | `actions/checkout`, `actions/setup-python`, `quarto-dev/quarto-actions/setup` | Checks out the code, installs Python/R environment and Quarto. |
| **2. Lint & Validate** | `lint` script, custom validation script | Runs static analysis on the code. A custom script validates that the YAML front matter of all `.qmd` files conforms to the defined schema. |
| **3. Graph Gen & Test** | Main Python parsing script, `graph-integrity` script | Generates `knowledge_graph.ttl`. Tests the generated graph for broken links or circular dependencies. |
| **4. Formal Verify (Opt.)** | `lake build`, Lean/Quarto comparison script | (If using Lean) Confirms all formal proofs are valid. Compares Lean and Quarto dependency graphs and reports inconsistencies. |
| **5. Render & Deploy** | `quarto render`, `actions/deploy-pages` | If all tests pass, builds the website with `quarto render`. Deploys the built static site and `knowledge_graph.ttl` to the publication target. |

### **B. Leveraging LLMs for Curation and Interaction**

Large Language Models (LLMs) are not a replacement for human curation but a powerful tool to amplify its capabilities. They excel at bridging the gap between unstructured text and structured graphs.

The quality of the graph depends on comprehensive and accurate links (`@label`), but authors, when writing proofs or explanations in natural language, often forget to add links. LLMs are adept at reading natural language and identifying the concepts mentioned [39]. This capability can be integrated into the CI pipeline as a "reviewer."

The proposed LLM integration strategy is as follows:

1. **Relationship Extraction Assistant (CI Integration):** When a pull request is opened, a GitHub Action sends the changed text to an LLM API. The prompt would be something like, "Read the following mathematical text and identify all mentioned mathematical concepts (e.g., 'group', 'homomorphism', 'compact space'). Compare this list with the explicit `@` links in the text and report any concepts that are mentioned but not linked." The response from the LLM is automatically posted as a comment on the pull request, prompting the author to add the links. This enforces adherence to the linking convention and improves the graph's comprehensiveness.
2. **Content Generation:** Use LLMs to generate first drafts of definition or example pages. A human expert then reviews, corrects, and refines the content. This significantly speeds up content creation.
3. **Natural Language Query Interface:** Deploy an LLM-powered chatbot using the Retrieval-Augmented Generation (RAG) pattern [40]. When a user asks a question in natural language like, "What theorems depend on the definition of a group?", the LLM translates it into a SPARQL query and executes it against the knowledge graph. It then integrates the results and generates a natural language answer with citations to the relevant wiki pages [41]. This allows even non-expert users to easily access the knowledge held by the graph.

## **IX. Integration and Strategic Roadmap**

### **A. Reconfirming the Integrated System**

The system detailed in this report forms a robust and evolvable knowledge ecosystem where each component works in concert. Quarto acts as the interface between humans and machines, and the Python pipeline transforms its content into formal knowledge. The RDF/OWL ontology ensures the structure of that knowledge, and Lean integration guarantees mathematical rigor. The SPARQL endpoint and API publish that knowledge to the world, and interactive visualizations enable intuitive exploration. Finally, automation with CI/CD and LLMs supports the growth and maintenance of this massive system.

### **B. Phased Implementation Plan**

To realistically advance this grand project, the following phased implementation plan is proposed:

* **Phase 1 (MVP: Minimum Viable Product):** Focus on establishing the core loop.
  * Define a minimal ontology for a limited mathematical field (e.g., basic group theory).
  * Create 50-100 nodes in Quarto under a strict linking convention.
  * Implement the Python parser to generate a static `knowledge_graph.ttl` file.
  * Set up a basic Quarto website and a CI/CD pipeline to render and deploy it.
* **Phase 2 (Querying and Visualization):**
  * Deploy the generated `knowledge_graph.ttl` to a Jena Fuseki server and publish a SPARQL endpoint.
  * Embed static Mermaid diagrams showing the local graph neighborhood of each node.
  * Develop an interactive D3.js/OJS visualization component and integrate it into key pages.
* **Phase 3 (Scaling and Intelligence):**
  * Integrate the formal verification workflow with Lean to build a verified subgraph.
  * Implement LLM-assisted relationship extraction in the CI pipeline.
  * Begin development of an RAG-based natural language Q&A interface.

### **C. Concluding Remarks on the Long-Term Vision**

This system has the potential to be not just a repository of knowledge, but a platform for discovery, education, and automated reasoning. By building from scratch with standard, interoperable components, the project becomes a future-proof asset adaptable to future technological advances. By combining meticulous curation with smart automation, we will build a "searchable database of mathematical results" and ultimately grow it into a truly interactive knowledge graph that reflects the entirety of mathematics.

#### **References**

[1] Knowledge Graphs - arXiv, accessed July 19, 2025, [http://arxiv.org/pdf/2003.02320](http://arxiv.org/pdf/2003.02320)
[2] MaRDI portal - Mathematical Research Data Initiative, accessed July 19, 2025, [https://portal.mardi4nfdi.de/](https://portal.mardi4nfdi.de/)
[3] Bravo MaRDI: A Wikibase Powered Knowledge Graph on ... - dblp, accessed July 19, 2025, [https://dblp.org/rec/journals/corr/abs-2309-11484](https://dblp.org/rec/journals/corr/abs-2309-11484)
[4] Bravo MaRDI: A Wikibase Knowledge Graph on Mathematics - Wikidata Workshop, accessed July 19, 2025, [https://wikidataworkshop.github.io/2023/papers/15__novel_bravo_mardi_a_wikibase_%5B1%5D.pdf](https://wikidataworkshop.github.io/2023/papers/15__novel_bravo_mardi_a_wikibase_%5B1%5D.pdf)
[5] Wikibase, Wikidata, and Knowledge Graphs - Professional Wiki, accessed July 19, 2025, [https://professional.wiki/en/wikibase-wikidata-and-knowledge-graphs](https://professional.wiki/en/wikibase-wikidata-and-knowledge-graphs)
[6] OntoMathPRO: An Ontology of Mathematical Knowledge, accessed July 19, 2025, [https://kpfu.ru/staff_files/F2070552642/S1064562422700016.pdf](https://kpfu.ru/staff_files/F2070552642/S1064562422700016.pdf)
[7] New components of the OntoMathPRO ontology for representing math knowledge, accessed July 19, 2025, [https://www.researchgate.net/publication/374853589_New_components_of_the_OntoMathPRO_ontology_for_representing_math_knowledge](https://www.researchgate.net/publication/374853589_New_components_of_the_OntoMathPRO_ontology_for_representing_math_knowledge)
[8] MaRDI Model Ontology classes and their relations. Visualisation done with Web-VOWL., accessed July 19, 2025, [https://www.researchgate.net/figure/MaRDI-Model-Ontology-classes-and-their-relations-Visualisation-done-with-Web-VOWL_fig3_373794021](https://www.researchgate.net/figure/MaRDI-Model-Ontology-classes-and-their-relations-Visualisation-done-with-Web-VOWL_fig3_373794021)
[9] Algorithm Knowledge Graph Ontology, accessed July 19, 2025, [https://algodata.mardi4nfdi.de/static/widoco/v1/index-en.html](https://algodata.mardi4nfdi.de/static/widoco/v1/index-en.html)
[10] Web Ontology Language - Wikipedia, accessed July 19, 2025, [https://en.wikipedia.org/wiki/Web_Ontology_Language](https://en.wikipedia.org/wiki/Web_Ontology_Language)
[11] The Mathematical Semantic Web - CiteSeerX, accessed July 19, 2025, [https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=8de81efaac59426eda2c9311c0db64d2c3e2120c](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=8de81efaac59426eda2c9311c0db64d2c3e2120c)
[12] Getting started with Apache Jena, accessed July 19, 2025, [https://jena.apache.org/getting_started/](https://jena.apache.org/getting_started/)
[13] Fuseki Quickstart - Apache Jena, accessed July 19, 2025, [https://jena.apache.org/documentation/fuseki2/fuseki-quick-start.html](https://jena.apache.org/documentation/fuseki2/fuseki-quick-start.html)
[14] Creating a Mathematical Knowledge Graph Using Lean 4's Mathlib ..., accessed July 19, 2025, [https://epikprotocol.medium.com/creating-a-mathematical-knowledge-graph-using-lean-4s-mathlib-library-b187d1af663c](https://epikprotocol.medium.com/creating-a-mathematical-knowledge-graph-using-lean-4s-mathlib-library-b187d1af663c)
[15] RDF Triple Stores vs. Property Graphs: What's the Difference? - Neo4j, accessed July 19, 2025, [https://neo4j.com/blog/knowledge-graph/rdf-vs-property-graphs-knowledge-graphs/](https://neo4j.com/blog/knowledge-graph/rdf-vs-property-graphs-knowledge-graphs/)
[16] RDFLib and Neo4j - Google Groups, accessed July 19, 2025, [https://groups.google.com/g/rdflib-dev/c/y5CweAwtHGE](https://groups.google.com/g/rdflib-dev/c/y5CweAwtHGE)
[17] OMV - Ontology Metadata Vocabulary, accessed July 19, 2025, [https://oeg.fi.upm.es/index.php/en/downloads/75-omv/index.html](https://oeg.fi.upm.es/index.php/en/downloads/75-omv/index.html)
[18] Ontology Metadata Vocabulary - NCBO BioPortal, accessed July 19, 2025, [https://bioportal.bioontology.org/ontologies/OMV](https://bioportal.bioontology.org/ontologies/OMV)
[19] Project Basics – Quarto, accessed July 19, 2025, [https://quarto.org/docs/projects/quarto-projects.html](https://quarto.org/docs/projects/quarto-projects.html)
[20] Cross References – Quarto, accessed July 19, 2025, [https://quarto.org/docs/authoring/cross-references.html](https://quarto.org/docs/authoring/cross-references.html)
[21] Front Matter - Quarto, accessed July 19, 2025, [https://quarto.org/docs/authoring/front-matter.html](https://quarto.org/docs/authoring/front-matter.html)
[22] 8 Setting options with YAML - Quarto: The Definitive Guide, accessed July 19, 2025, [https://quarto-tdg.org/yaml.html](https://quarto-tdg.org/yaml.html)
[23] Python Frontmatter ��� Python Frontmatter 1.0.0 documentation, accessed July 19, 2025, [https://python-frontmatter.readthedocs.io/](https://python-frontmatter.readthedocs.io/)
[24] python-frontmatter - PyPI, accessed July 19, 2025, [https://pypi.org/project/python-frontmatter/](https://pypi.org/project/python-frontmatter/)
[25] Generating Millions Of Lean Theorems With Proofs By Exploring State Transition Graphs, accessed July 19, 2025, [https://arxiv.org/html/2503.04772v1](https://arxiv.org/html/2503.04772v1)
[26] Topic: Dependency Graph - Zulip Chat Archive, accessed July 19, 2025, [https://leanprover-community.github.io/archive/stream/113488-general/topic/Dependency.20Graph.html](https://leanprover-community.github.io/archive/stream/113488-general/topic/Dependency.20Graph.html)
[27] Getting Started — LeanDojo 4.20.0 documentation, accessed July 19, 2025, [https://leandojo.readthedocs.io/en/latest/getting-started.html](https://leandojo.readthedocs.io/en/latest/getting-started.html)
[28] Apache Jena Fuseki, accessed July 19, 2025, [https://jena.apache.org/documentation/fuseki2/](https://jena.apache.org/documentation/fuseki2/)
[29] Creating RESTful APIs Using SPARQL A Detailed and In-Depth Step-by-Step Tutorial for Developers - MoldStud, accessed July 19, 2025, [https://moldstud.com/articles/p-creating-restful-apis-using-sparql-a-detailed-and-in-depth-step-by-step-tutorial-for-developers](https://moldstud.com/articles/p-creating-restful-apis-using-sparql-a-detailed-and-in-depth-step-by-step-tutorial-for-developers)
[30] How to Use the SPARQL Endpoint - PoolParty Semantic Suite Documentation, accessed July 19, 2025, [https://help.poolparty.biz/en/developer-guide/basic---advanced-server-apis/poolparty-s-sparql-endpoint/how-to-use-the-sparql-endpoint.html](https://help.poolparty.biz/en/developer-guide/basic---advanced-server-apis/poolparty-s-sparql-endpoint/how-to-use-the-sparql-endpoint.html)
[31] Introduction to Neo4j & GraphQL | Development | Free Neo4j Courses from GraphAcademy, accessed July 19, 2025, [https://graphacademy.neo4j.com/courses/graphql-basics/](https://graphacademy.neo4j.com/courses/graphql-basics/)
[32] Introduction - Neo4j GraphQL Library, accessed July 19, 2025, [https://neo4j.com/docs/graphql/current/](https://neo4j.com/docs/graphql/current/)
[33] Interactivity - Quarto, accessed July 19, 2025, [https://quarto.org/docs/interactive/](https://quarto.org/docs/interactive/)
[34] Observable JS - Quarto, accessed July 19, 2025, [https://quarto.org/docs/interactive/ojs/](https://quarto.org/docs/interactive/ojs/)
[35] D3 by Observable | The JavaScript library for bespoke data ..., accessed July 19, 2025, [https://d3js.org/](https://d3js.org/)
[36] htmlwidgets for R - Quarto, accessed July 19, 2025, [https://quarto.org/docs/interactive/widgets/htmlwidgets.html](https://quarto.org/docs/interactive/widgets/htmlwidgets.html)
[37] Quarto Render · Actions · GitHub Marketplace · GitHub, accessed July 19, 2025, [https://github.com/marketplace/actions/quarto-render](https://github.com/marketplace/actions/quarto-render)
[38] Publishing with Continuous Integration (CI) - Quarto, accessed July 19, 2025, [https://quarto.org/docs/publishing/ci.html](https://quarto.org/docs/publishing/ci.html)
[39] SKG-LLM: Developing a Mathematical Model for Stroke ... - arXiv, accessed July 19, 2025, [https://arxiv.org/abs/2503.06475](https://arxiv.org/abs/2503.06475)
[40] AI Semantic Credibility and Wikibase Knowledge Graph Self-Veriﬁcation - iPRES 2024, accessed July 19, 2025, [https://ipres2024.pubpub.org/pub/93xgtzp9](https://ipres2024.pubpub.org/pub/93xgtzp9)
[41] Graph-Augmented Reasoning: Evolving Step-by-Step ... - arXiv, accessed July 19, 2025, [https://arxiv.org/abs/2503.01642](https://arxiv.org/abs/2503.01642)
