
# **ゼロから構築する本格的な数学ナレッジグラフ**

## **I. 序論：セマンティックな数学的ウィキのための原則的フレームワーク**

### **A. プロジェクトのビジョンと目標**

数学の全分野を網羅する、進化し続けるクエリ可能なウィキをナレッジグラフとして構築するという目標は、数学的知識の構造化とアクセス可能性におけるパラダイムシフトを意味します。その核心は、公理、定義、定理、そして例を相互に接続されたノードとして表現し、ユーザー（および機械）が「この公理に依存する定理は何か」といった関係性を問い合わせたり、新たな繋がりを発見したりできるシステムを創出することにあります 1。この構想は、単なる文書リポジトリではなく、数学の論理的構造そのものを反映した「セマンティックウィキ」あるいは「検索可能な数学的成果のデータベース」を構築することを目指すものです。

この野心的な目標を達成するために、本レポートでは「スクラッチからの構築」アプローチを提案します。MaRDI（Mathematical Research Data Initiative）のような先進的なプロジェクトでは、Wikibase（カスタマイズされたWikipedia）プラットフォーム上で数百万の数学的アイテムをリンクさせる包括的なナレッジグラフが構築されています 2。このアプローチは既存の強力なプラットフォームを活用する点で優れていますが 5、本レポートで詳述するスクラッチからの構築アプローチは、技術スタック、データモデル、そして最終的なユーザーエクスペリエンスに対する完全な制御を可能にし、プロジェクト固有の要件に最適化されたシステムを実現するという、かけがえのない利点を提供します。

### **B. 統合的アーキテクチャの理念**

提案するアーキテクチャは、以下の4つのフェーズからなる好循環（virtuous cycle）を基本理念として設計されています。

1. **オーサリング（Quarto）:** 人間が構造化され、可読性の高いコンテンツを作成します。  
2. **抽出（Python）:** 自動化されたスクリプトがこのコンテンツを解析し、形式的なグラフ構造に変換します。  
3. **クエリ（SPARQL/API）:** 生成されたグラフは、探索と分析のために公開されます。  
4. **エンリッチメント（可視化 & LLM）:** グラフから得られた知見がオーサリング環境にフィードバックされ、インテリジェントなアシスタント機能の動力源となります。

このアーキテクチャは、初期段階からスケーラビリティ、メンテナンス性、拡張性を確保するように設計されており、数学という広大な領域を段階的に取り込んでいく長期的なプロジェクトの基盤として機能します。

### **C. 本レポートの構成とロードマップ**

本レポートは、このビジョンを実現するための具体的な設計図として構成されています。まず、ナレッジグラフの論理的基盤となるオントロジーの設計から始めます。次に、Quartoを用いた効率的なコンテンツ作成手法を詳述し、それをPythonベースのパイプラインで形式的なグラフデータに変換するプロセスを具体的に示します。さらに、Lean 4証明支援系との連携による厳密性の確保、SPARQLエンドポイントを介したデータの公開とクエリ、そしてグラフの可視化によるインタラクティブな探索体験の実現方法について論じます。最後に、CI/CDパイプラインと大規模言語モデル（LLM）を活用した自動化とスケーラビリティ確保の戦略を提示し、プロジェクト全体の統合と段階的な実装計画をもって締めくくります。

## **II. 基礎設計：数学的オントロジーの構築**

### **A. オントロジーの中心的な役割**

ナレッジグラフの構築における最初の、そして最も重要なステップは、その「スキーマ」となるオントロジーを定義することです。オントロジーは、グラフ内に存在する「モノ」の種類（クラス）と、それらの間の「関係性」の種類（プロパティ）を形式的に定義するものです 1。これはシステム全体の設計思想の礎であり、データの一貫性を保証し、論理的な推論を可能にするための根幹をなします。OntoMathPRO 6 やMaRDI 8 といった主要な数学知識プロジェクトが、その基盤として精緻なオントロジーを構築している事実は、このステップの重要性を物語っています。

### **B. 中核となるノードと関係の型**

数学的知識ドメインのために、以下の主要なノード（クラス）と関係（プロパティ）を定義します。

* **ノード型（クラス）:**  
  * Axiom（公理）  
  * Definition（定義）  
  * Theorem（定理）: Lemma（補題）、Proposition（命題）、Corollary（系）を含む。  
  * Example（例）  
* **関係型（プロパティ）:**  
  * uses / dependsOn: 最も重要な関係であり、依存関係グラフを形成します（例：定理が定義をusesする）。  
  * hasExample / isExampleOf: 概念と具体的な実例を結びつけます。  
  * generalizes / specializes: 概念間の階層関係を捉えます。  
  * implies: 定理に内在する、より具体的な論理的含意関係を示します。

### **C. アーキテクチャ決定：RDF対プロパティグラフ**

プロジェクトの要件として「データをLinked Dataとして公開する」ことが明記されている点は、技術選定における決定的な要因となります。この要件を最も忠実かつ直接的に満たすためには、RDF（Resource Description Framework）ネイティブなアプローチが最適です。

Linked Dataは、URI、HTTP、そしてRDFというW3C標準技術に基づいています 10。

rdflibのようなライブラリやApache Jena Fusekiのようなトリプルストアは、まさにこの目的のために設計されたツールです 12。一方で、Leanナレッジグラフプロジェクトで採用されているNeo4jのようなプロパティグラフは非常に強力ですが、RDFネイティブではありません 14。プロパティグラフのモデル（ノードとエッジの両方にキーバリュー形式のプロパティを持つ）は、RDFのトリプル（主語-述語-目的語）モデルとは根本的に異なります 15。

rdflib-neo4j 16 のようなブリッジは存在しますが、これらは追加の変換レイヤーを導入することになり、インピーダンスミスマッチ（impedance mismatch）のリスクを伴います。

したがって、主要な目標であるLinked Data公開を、最高の忠実度と最小の複雑性で達成するためには、中核となるデータモデルとしてRDFを採用することが論理的な帰結となります。本プロジェクトはRDFファースト戦略をとり、ナレッジグラフはRDFトリプルの集合としてネイティブに表現されるべきです。

**表1：ナレッジグラフモデルの比較（RDF vs. プロパティグラフ）**

| 評価基準 | RDF (Resource Description Framework) | プロパティグラフ (例: Neo4j) |
| :---- | :---- | :---- |
| **W3C標準** | ○ (RDF, RDFS, OWL, SPARQL) | × (GQLがISO標準化中) |
| **Linked Dataネイティブサポート** | ○ (基本設計思想) | △ (変換レイヤーが必要) |
| **クエリ言語** | SPARQL | Cypher, GQL |
| **スキーマ** | RDFS/OWLによる形式的定義 | 暗黙的または制約による定義 |
| **ツールエコシステム** | 学術、オープンデータ分野で成熟 | エンタープライズ、分析分野で成熟 |
| **データモデル** | 主語-述語-目的語のトリプル | プロパティを持つノードと関係 |

### **D. RDF/OWLによるオントロジーの形式化**

具体的なオントロジーファイル（例：math-ontology.ttl）を作成する計画は以下の通りです。まず、カスタム名前空間を定義します（例：PREFIX mymath: \<<https://mathwiki.org/ontology\#\>）。次に、OWL/RDFSを用いて中核となるクラスとプロパティを定義します。>

コード スニペット

@prefix rdf: \<<http://www.w3.org/1999/02/22-rdf-syntax-ns\#\>>.  
@prefix rdfs: \<<http://www.w3.org/2000/01/rdf-schema\#\>>.  
@prefix owl: \<<http://www.w3.org/2002/07/owl\#\>>.  
@prefix skos: \<<http://www.w3.org/2004/02/skos/core\#\>>.  
@prefix mymath: \<<https://mathwiki.org/ontology\#\>>.

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

さらに、車輪の再発明を避け、相互運用性を劇的に向上させるために、カスタムオントロジーを既存の確立されたオントロジーにマッピングすることが不可欠です。OntoMathPRO 6 やOMV (Ontology Metadata Vocabulary) 17 のようなプロジェクトは、数学的知識のモデリングに関して広範な研究を行っています。これらの外部スキーマのクラスやプロパティに対して

owl:equivalentClass や rdfs:subClassOf を用いてリンクすることで、我々のグラフは作成された瞬間から、より広範なLinked Open Dataクラウドにおけるセマンティックな文脈を獲得します。これは、機械可読性と外部システムとの統合において計り知れない利点となります。

**表2：中核となる数学オントロジーのスキーマ**

| ラベル | 型 | URI | RDFSコメント | 外部マッピング (例) |
| :---- | :---- | :---- | :---- | :---- |
| Theorem | Class | mymath:Theorem | 証明された数学的言明 | owl:equivalentClass ontomathpro:Theorem |
| Definition | Class | mymath:Definition | 概念の意味を定める言明 | owl:equivalentClass ontomathpro:Definition |
| Axiom | Class | mymath:Axiom | 証明なしに真とされる言明 | owl:equivalentClass ontomathpro:Axiom |
| Example | Class | mymath:Example | 概念や定理を具体的に示すもの | rdfs:subClassOf skos:Concept |
| uses | Property | mymath:uses | 主語が目的語を証明や定義で利用する | rdfs:subPropertyOf skos:related |
| hasExample | Property | mymath:hasExample | 主語が目的語を例として持つ | rdfs:subPropertyOf skos:related |

## **III. オーサリング環境：Quartoでグラフを織りなす**

### **A. 指導原則：人間によるエッジのキュレーション**

ナレッジグラフの信頼性は、規律あるオーサリングに懸かっています。グラフのエッジ（関係性）を生成する主要なメカニズムは、著者による明示的かつ手動のリンク作成です。この人間によるキュレーションが、高品質なグラフの基盤となります。

### **B. ファイルとディレクトリの構造**

「1コンセプト、1ファイル」ポリシーを推奨します。例えば、definitions/def-group.qmd、theorems/thm-group-isomorphism.qmd のように、各数学的オブジェクトに個別のファイルを与えます。この構造は、Quartoのプロジェクトレベルのメタデータ機能を活用することで、さらなる自動化と一貫性の向上に繋がります。

Quartoプロジェクトでは、サブディレクトリ内に \_metadata.yml ファイルを配置することで、そのディレクトリ内の全ドキュメントに共通のメタデータを適用できます 19。この機能を利用し、コンテンツを数学の分野ごと（例：

/algebra、/topology）に整理します。/algebra ディレクトリ内に domain: "Algebra" という内容の \_metadata.yml を置けば、後述する解析スクリプトがこのメタデータを読み取り、そのディレクトリ内の全てのノードに対して自動的に mymath:def-group mymath:hasDomain "Algebra" のようなトリプルを追加できます。これにより、著者の負担を軽減し、分類の一貫性を保証する自動化レイヤーが実現します。

### **C. Quartoクロスリファレンスの習得**

各ノードの作成と参照には、Quartoのクロスリファレンス機能を徹底的に活用します。全ての定理、定義などには、一意のラベル（例：{\#def-group}）を付与する必要があります 20。そして、オーサリングにおける核となるルールを次のように定めます。

**「他の概念を参照する際は、必ず @ 構文（例：@def-group）を使用すること。」**

この規約を遵守することで、QuartoはHTML出力時に標準的なハイパーリンクを生成し、このリンクがバックエンドのパーサーによってグラフのエッジとして解釈される、という明確なパイプラインが確立されます。

### **D. YAMLフロントマターへの機械可読メタデータの埋め込み**

Quartoは、.qmd ファイルの先頭にあるYAMLフロントマターの一部のキーを解釈しますが、それ以外のカスタムキーは無視します 21。この性質を利用して、グラフ構築に必要な独自のメタデータを各ファイルに埋め込みます。

python-frontmatter 23 のようなライブラリを使えば、このカスタムメタデータを容易に抽出できます。

各 .qmd ファイルのYAMLヘッダーには、以下の標準キーセットを含めることを提案します。

**表3：Quartoノードメタデータ仕様**

| キー | 型 | 説明 |
| :---- | :---- | :---- |
| title | String | 人間が読むためのノードのタイトル（例：「定義：群」）。 |
| id | String | ノードの一意で安定した識別子。クロスリファレンスラベルと一致させる（例：def-group）。 |
| type | String | オントロジー上のノードの型（例：Definition, Theorem）。パーサーにとって不可欠。 |
| status | String | コンテンツの成熟度（例：stub, draft, complete, verified）。 |
| lean\_id | String | (任意) 対応するLeanライブラリ内の形式的証明の識別子。形式的検証レイヤーとの連携に使用。 |
| requires | Array | (任意) 依存関係IDの明示的なリスト。本文中のリンクを補完し、公理のような暗黙的な依存関係に有用。 |

以下に、完全な .qmd ファイルヘッダーの例を示します。

YAML

\---  
title: "Definition: Group"  
id: "def-group"  
type: "Definition"  
status: "complete"  
lean\_id: "Mathlib.GroupTheory.Group.group"  
requires:  
  \- "def-set"  
  \- "def-binary-operation"  
\---

A group is a set equipped with a binary operation that combines any two elements to form a third element in such a way that four conditions called group axioms are satisfied, namely closure, associativity, identity and invertibility.  
...

## **IV. バックエンドパイプライン：Quartoドキュメントからクエリ可能なグラフへ**

### **A. パイプラインアーキテクチャの概要**

バックエンドの処理パイプラインは、以下のステップで構成されます。

1. プロジェクト内の .qmd ファイルをスキャンする。  
2. 各ファイルについて、YAMLフロントマターとMarkdownコンテンツを解析する。  
3. ノード情報（ID、型、タイトルなど）と関係（@リンクやrequiresリスト）を抽出する。  
4. 抽出された情報に基づいてRDFトリプルを構築する。  
5. 構築されたグラフ全体を標準的なグラフ形式（例：Turtle）でシリアライズ（ファイルに出力）する。

### **B. 解析戦略：生Markdown対レンダリング済みHTML**

コンテンツからグラフ構造を抽出するには、主に2つのアプローチが考えられます。

* **アプローチ1（推奨）：生.qmdファイルの解析**  
  * **ツール:** Pythonライブラリ python-frontmatter 23 を使用して、YAMLメタデータとMarkdownコンテンツを簡単に分離します。  
  * **利点:** 完全なQuartoレンダリングを回避できるため高速です。メタデータや @label リンクといった「真実のソース」に直接アクセスできます。  
  * **欠点:** Markdown本文中のすべての @label 参照を見つけるために、堅牢な正規表現またはAST（抽象構文木）パーサーが必要になります。  
* **アプローチ2：レンダリング済みHTMLの解析**  
  * **ツール:** Leanナレッジグラフプロジェクトで見られるように、Pythonの BeautifulSoup ライブラリを使用します 14。  
  * **利点:** Quartoがすべてのクロスリファレンスを href 属性を持つ標準的な \<a\> タグに解決してくれるため、リンクの抽出が単純化されます。  
  * **欠点:** quarto render の実行が必要なため低速です。また、HTMLの解析はMarkdownの解析よりも変更に弱い（brittle）可能性があります。

**推奨:** 速度と直接性の観点から、生 .qmd ファイルの解析から始めることを推奨します。python-frontmatter ライブラリはメタデータの扱いに理想的であり、@label の抽出は対象を絞った正規表現で十分に処理可能です。

### **C. rdflibによるグラフの構築**

以下に、Pythonとrdflibライブラリを用いてグラフを構築するプロセスの骨子を示します。

Python

import frontmatter  
import re  
from pathlib import Path  
from rdflib import Graph, Literal, Namespace, RDF, RDFS

\# 名前空間の定義  
MYMATH \= Namespace("<https://mathwiki.org/ontology\#>")  
BASE\_URI \= "<https://mathwiki.org/resource/>"

\# グラフの初期化  
g \= Graph()  
g.bind("mymath", MYMATH)  
g.bind("rdfs", RDFS)

\# クロスリファレンスを抽出する正規表現  
crossref\_pattern \= re.compile(r'@(\[a-zA-Z0-9\_-\]+)')

\# qmdファイルのスキャンと処理  
for qmd\_path in Path("content/").rglob("\*.qmd"):  
    with open(qmd\_path, 'r', encoding='utf-8') as f:  
        post \= frontmatter.load(f)  
        metadata \= post.metadata  
        content \= post.content

    if 'id' not in metadata or 'type' not in metadata:  
        continue \# 必須メタデータがないファイルはスキップ

    node\_id \= metadata\['id'\]  
    node\_uri \= Namespace(BASE\_URI)\[node\_id\]

    \# 1\. ノードの型とラベルのトリプルを追加  
    g.add((node\_uri, RDF.type, MYMATH\[metadata\['type'\]\]))  
    if 'title' in metadata:  
        g.add((node\_uri, RDFS.label, Literal(metadata\['title'\], lang='en')))

    \# 2\. 本文中の@リンクから依存関係を抽出  
    dependencies \= set(crossref\_pattern.findall(content))

    \# 3\. YAMLのrequiresからも依存関係を追加  
    if 'requires' in metadata and isinstance(metadata\['requires'\], list):  
        dependencies.update(metadata\['requires'\])

    \# 4\. 依存関係のトリプルを追加  
    for dep\_id in dependencies:  
        dep\_uri \= Namespace(BASE\_URI)\[dep\_id\]  
        g.add((node\_uri, MYMATH.uses, dep\_uri))

\# グラフのシリアライズ  
g.serialize(destination='knowledge\_graph.ttl', format\='turtle')

print("Knowledge graph generated successfully.")

### **D. データシリアライゼーションと保存**

上記のスクリプトの最終ステップで、構築されたグラフ全体が g.serialize() を用いてTurtle（.ttl）形式のファイルに出力されます。この knowledge\_graph.ttl ファイルがバックエンドパイプラインの主要な成果物となり、次のフェーズである公開やトリプルストアへのロードの準備が整ったことになります。

## **V. 形式的検証と厳密性：Lean 4エコシステムの統合**

### **A. 「グラウンドトゥルース」としての依存関係グラフ**

Leanのような証明支援系は、その内部に100%正確な依存関係グラフを保有しています。これは、新しい定理を証明する際に、コンパイラがどの補題が使用されたかを厳密に知る必要があるためです 25。この形式的に検証された依存関係は、我々のナレッジグラフにとって、非常に忠実度の高い貴重なデータソースとなります。

### **B. Leanリポジトリからのデータ抽出**

このタスクには、**LeanDojo** が主要なツールとして推奨されます 27。LeanDojoのドキュメントに示されているように、

mathlib のようなLeanプロジェクトに対して trace コマンドを実行することで、詳細な依存関係データを抽出できます。特に重要な出力ファイルは、ファイルレベルの依存関係を示す \*.dep\_paths と、より詳細なタクティクや定理レベルの情報を含む \*.trace.xml です。これらが形式的なナレッジグラフを構築するための生データとなります。

### **C. 形式的グラフと非形式的グラフの架け橋**

これら二つの世界（人間が記述したQuartoグラフと、Leanが生成した形式的グラフ）を繋ぐ鍵は、前述のQuarto YAMLメタデータで提案した lean\_id フィールドです。

この架け橋は、以下の検証・エンリッチメントワークフローを可能にします。まず、QuartoグラフとLeanDojoの出力を両方解析する二次的なPythonスクリプトを用意します。このスクリプトは、Quartoの定理ノードに lean\_id（例：Mathlib.Data.Real.Basic.mul\_comm）を見つけると、それをキーとしてLeanの依存関係グラフを検索します。そして、Leanのグラフに記録されている依存関係と、Quartoグラフ内の mymath:uses 関係を比較します。

### **D. 検証とエンリッチメントのワークフロー**

この比較プロセスにより、以下のような高度な検証が可能になります。

1. **不整合の検出:** Leanの証明で使用されている依存関係が、Quartoのテキストでリンクされていない場合（またはその逆）、スクリプトはこれを「不整合」としてフラグを立て、人間のレビューを促します。これにより、ドキュメントの論理的な欠陥や記述漏れを体系的に発見できます。  
2. **検証済みトリプルの追加:** 依存関係が一致した場合、スクリプトはQuartoグラフに mymath:isVerifiedBy という新しいトリプルを追加します。このトリプルは、Quartoの定理ノードを、形式的なLeanの証明を表す新しいノードにリンクします。これにより、グラフ内に「形式的に検証済み」のサブグラフが形成され、知識の信頼性が格段に向上します。

このワークフローを通じて、人間が作成した知識と機械が検証した知識が融合し、ナレッジグラフは単なる情報の集合から、信頼性の高い論理体系へと昇華します。

## **VI. 公開とクエリ：ナレッジをLinked Dataとして公開する**

### **A. Apache Jena FusekiによるSPARQLエンドポイントの展開**

構築したナレッジグラフを世界中のアプリケーションやユーザーが利用できるようにするため、SPARQLエンドポイントを公開します。Apache Jena Fusekiは、この目的のための堅牢で標準的なトリプルストアサーバーです。Fusekiのクイックスタートガイドに基づき、以下の手順でセットアップします 13。

1. Fusekiサーバーをダウンロードし、起動します。  
2. Webベースの管理UI（通常は <http://localhost:3030/）にアクセスし、新しいデータセット（インメモリまたは永続的なTDB）を作成します。>  
3. バックエンドパイプラインで生成された knowledge\_graph.ttl ファイルを、作成したデータセットにアップロードします。

これにより、データセットごとに専用のSPARQLクエリUIが利用可能になり、グラフに対するライブクエリの準備が整います。

### **B. ライブクエリの有効化**

SPARQLエンドポイントは、HTTPを介してグラフに問い合わせるための標準的なインターフェースを提供します。これにより、プロジェクトの目標に沿った様々な質問に答えることができます。

* **例1：選択公理に依存する全ての定理を検索**  
  コード スニペット  
  PREFIX mymath: \<<https://mathwiki.org/ontology\#\>>  
  PREFIX base: \<<https://mathwiki.org/resource/\>>

  SELECT?theorem\_label  
  WHERE {  
   ?theorem mymath:uses base:axiom-of-choice.  
   ?theorem rdfs:label?theorem\_label.  
  }

* **例2：特定の定理の完全な依存関係チェーンを検索（推移的クエリ）**  
  コード スニペット  
  PREFIX mymath: \<<https://mathwiki.org/ontology\#\>>  
  PREFIX base: \<<https://mathwiki.org/resource/\>>

  SELECT DISTINCT?dependency\_label  
  WHERE {  
    base:thm-pythagorean mymath:uses+?dependency.  
   ?dependency rdfs:label?dependency\_label.  
  }

  (uses+ は1回以上の uses 関係の連鎖を意味します)

### **C. ユーザーフレンドリーなクエリAPIの作成（任意だが推奨）**

SPARQLは強力ですが、多くのエンドユーザーにとっては複雑すぎる場合があります。より広範な利用を促進するために、SPARQLエンドポイントの上にシンプルなAPIラッパーを構築することが有効です。

* **REST API:** Pythonのフレームワーク（FlaskやFastAPI）を使用して、/api/dependencies?id=thm-pythagorean のような直感的なエンドポイントを作成します 29。このエンドポイントは、内部で事前に定義されたSPARQLクエリを実行し、結果を整形されたJSONとして返します。  
* **GraphQL API:** より複雑なクライアントサイドの要求に応えるためには、GraphQLが適しています。GraphQLは、クライアントが必要なデータを正確に指定できる、強く型付けされたクエリ言語です。neo4j-graphql 31（Neo4j使用時）や、汎用のGraphQL-to-SPARQLライブラリを利用して、オントロジーをGraphQLスキーマとして公開することができます。これにより、特にフロントエンド開発者にとって、データへのアクセスが大幅に簡素化されます。

## **VII. インタラクティブな探索：ナレッジグラフの可視化**

### **A. ナレッジループを閉じる**

ナレッジグラフの真価は、その構造をユーザーが直感的に理解し、探索できるようになったときに発揮されます。抽象的なグラフ構造を具体的なビジュアルとしてQuartoページに埋め込むことで、この「ナレッジループ」を閉じ、偶発的な発見（serendipitous discovery）を促進します。

### **B. Mermaidによる静的・簡易的な可視化**

Quartoは、テキストベースの図表作成ツールであるMermaidをネイティブでサポートしています 20。これを利用して、各ノードページのコンテキストを視覚的に示すことができます。CI/CDパイプラインの一部として、各ノード（例：

def-group）に対してSPARQLクエリを実行し、そのノードから1ホップ先にある全てのノード（依存先と被依存元）を取得します。そして、その結果からMermaidの graph TD 構文を自動生成し、対応する .qmd ファイルにレンダリング前に挿入します。これにより、各ページにそのページの概念が全体の構造の中でどのような位置づけにあるかを示す静的な依存関係図を簡単に埋め込むことができます。

### **C. 動的・インタラクティブな可視化**

よりリッチな探索体験を提供するためには、ユーザーが操作できるインタラクティブなグラフが理想的です。QuartoがObservable JS（OJS）とhtmlwidgetsをサポートしているおかげで、複雑なサーバーサイドのレンダリングを必要とせずに、これを実現できます 33。

このアプローチの鍵は、クライアントサイドでの処理です。Quartoは {ojs} コードブロック内のJavaScriptをユーザーのブラウザで直接実行できます 34。D3.js 35 やVis.jsのようなライブラリは、Webベースのグラフ可視化における標準ツールです。

具体的な実装戦略は以下の通りです。

1. **データ生成:** バックエンドパイプラインまたはCI/CDパイプラインにおいて、各ノードページ（例：def-group.qmd）に対応する小さなJSONファイル（例：def-group.json）を生成します。このJSONファイルには、そのノードのローカルなグラフ近傍（例：2ホップ以内のノードとエッジ）のデータが含まれます。  
2. **可視化コンポーネントの作成:** 再利用可能なOJSコードチャンクを作成します。このチャンクは、D3.jsライブラリを require し、ページに対応するJSONファイルを非同期で読み込み、インタラクティブな力学モデル（force-directed layout）のグラフとしてレンダリングします。  
3. **埋め込み:** このOJSチャンクを、関連する情報を表示したいQuartoページに含めます。

この方法により、可視化ロジックは再利用可能になり、データ読み込みは各ページで必要な分だけ行われるため効率的です。また、RやPythonを主に使用する開発者向けには、pyvis（Python）やvisNetwork（R）のようなライブラリが、自己完結型のインタラクティブなHTMLウィジェットを生成し、これをQuartoがコードチャンクから直接埋め込むことも可能です 36。

## **VIII. 自動化とスケーラビリティ：CI/CDパイプラインとLLM支援キュレーション**

### **A. システムのバックボーンとしてのCI/CDパイプライン**

この規模のプロジェクトを管理・維持するためには、徹底した自動化が不可欠です。GitHub Actionsと公式のQuartoアクション 37 を用いて、堅牢な継続的インテグレーション／継続的デプロイメント（CI/CD）パイプラインを構築します。このパイプラインが、システム全体の品質と一貫性を保証するバックボーンとなります。

**表4：CI/CDパイプラインのステージとアクション**

| ステージ | アクション | 説明 |
| :---- | :---- | :---- |
| **1\. セットアップ** | actions/checkout, actions/setup-python, quarto-dev/quarto-actions/setup | コードをチェックアウトし、Python/R環境とQuartoをインストールします。 |
| **2\. リントと検証** | lint スクリプト, カスタム検証スクリプト | コードの静的解析を実行します。カスタムスクリプトで、全.qmdファイルのYAMLフロントマターが定義済みスキーマに準拠しているか検証します。 |
| **3\. グラフ生成とテスト** | メインのPython解析スクリプト, graph-integrity スクリプト | knowledge\_graph.ttl を生成します。生成されたグラフに壊れたリンクや循環依存がないかテストします。 |
| **4\. 形式的検証 (任意)** | lake build, Lean/Quarto比較スクリプト | (Lean使用時) 全ての形式的証明が有効であることを確認します。LeanとQuartoの依存関係グラフを比較し、不整合を報告します。 |
| **5\. レンダリングとデプロイ** | quarto render, actions/deploy-pages | 全てのテストが成功した場合、quarto renderでWebサイトをビルドします。ビルドされた静的サイトとknowledge\_graph.ttlを公開先にデプロイします。 |

### **B. キュレーションとインタラクションのためのLLM活用**

大規模言語モデル（LLM）は、人間のキュレーションを代替するものではなく、その能力を増幅させる強力なツールです。特に、非構造化テキストと構造化グラフの間のギャップを埋める能力に優れています。

グラフの品質は、網羅的で正確なリンク（@label）に依存しますが、著者は自然言語で証明や説明を記述する際に、リンクの追加を忘れがちです。LLMは自然言語を読み解き、言及されている概念を特定することに長けています 39。この能力をCIパイプラインに「査読者」として組み込むことができます。

提案するLLM統合戦略は以下の通りです。

1. **関係抽出アシスタント（CI連携）:** プルリクエストがオープンされると、GitHub Actionが変更されたテキストをLLM APIに送信します。その際のプロンプトは、「以下の数学的テキストを読み、言及されている全ての数学的概念（例：'群', '準同型', 'コンパクト空間'）を特定してください。このリストを、テキスト中の明示的な@リンクと比較し、言及されているにもかかわらずリンクされていない概念を報告してください。」といったものになります。LLMからの応答は、自動的にプルリクエストにコメントとして投稿され、著者にリンクの追加を促します。これにより、リンク規約の遵守が徹底され、グラフの網羅性が向上します。  
2. **コンテンツ生成:** LLMを用いて、定義や例のページの初稿を生成させます。その後、人間の専門家がその内容をレビューし、修正・改良します。これにより、コンテンツ作成の速度が大幅に向上します。  
3. **自然言語クエリインターフェース:** 検索拡張生成（Retrieval-Augmented Generation, RAG）パターンを用いたLLM搭載のチャットボットをデプロイします 40。ユーザーが「群の定義に依存する定理は何ですか？」のような自然言語で質問すると、LLMはそれをSPARQLクエリに変換し、ナレッジグラフに対して実行します。そして、得られた結果を統合し、関連するウィキページへの引用付きで自然言語の回答を生成します 41。これにより、専門家でないユーザーでもグラフの持つ知識を容易に引き出すことが可能になります。

## **IX. 統合と戦略的ロードマップ**

### **A. 統合システムの再確認**

本レポートで詳述したシステムは、各コンポーネントが協調して動作することで、堅牢かつ進化可能な知識エコシステムを形成します。Quartoは人間と機械の間のインターフェースとして機能し、Pythonパイプラインがその内容を形式知に変換します。RDF/OWLオントロジーがその知識の構造を保証し、Lean連携が数学的な厳密性を担保します。SPARQLエンドポイントとAPIがその知識を世界に公開し、インタラクティブな可視化が直感的な探索を可能にします。そして、CI/CDとLLMによる自動化が、この巨大なシステムの成長と維持を支えます。

### **B. 段階的実装計画**

この壮大なプロジェクトを現実的に進めるため、以下の段階的な実装計画を提案します。

* **フェーズ1（MVP：Minimum Viable Product）:** コアループの確立に集中します。  
  * 限定的な数学分野（例：基本的な群論）のための最小限のオントロジーを定義します。  
  * 厳密なリンク規約のもと、50〜100程度のノードをQuartoで作成します。  
  * Pythonパーサーを実装し、静的な knowledge\_graph.ttl ファイルを生成します。  
  * 基本的なQuarto Webサイトと、それをレンダリング・デプロイするCI/CDパイプラインをセットアップします。  
* **フェーズ2（クエリと可視化）:**  
  * 生成された knowledge\_graph.ttl をJena Fusekiサーバーにデプロイし、SPARQLエンドポイントを公開します。  
  * 各ノードのローカルなグラフ近傍を示す静的なMermaid図を埋め込みます。  
  * インタラクティブなD3.js/OJS可視化コンポーネントを開発し、主要なページに統合します。  
* **フェーズ3（スケーリングとインテリジェンス）:**  
  * Leanによる形式的検証ワークフローを統合し、検証済みサブグラフを構築します。  
  * CIパイプラインにLLM支援による関係抽出機能を実装します。  
  * RAGベースの自然言語Q\&Aインターフェースの開発に着手します。

### **C. 長期的ビジョンに関する結びの言葉**

本システムは、単なる知識のリポジトリに留まらず、発見、教育、そして自動推論のためのプラットフォームとなる潜在能力を秘めています。標準的で相互運用可能なコンポーネントを用いてスクラッチから構築することにより、プロジェクトは将来の技術的進歩にも適応可能な、未来志向の資産となります。綿密なキュレーションと賢明な自動化を組み合わせることで、「検索可能な数学的成果のデータベース」を構築し、最終的には数学の全貌を映し出す真にインタラクティブなナレッジグラフへと成長していくことでしょう。

#### **引用文献**

1. Knowledge Graphs \- arXiv, 7月 19, 2025にアクセス、 [http://arxiv.org/pdf/2003.02320](http://arxiv.org/pdf/2003.02320)  
2. MaRDI portal \- Mathematical Research Data Initiative, 7月 19, 2025にアクセス、 [https://portal.mardi4nfdi.de/](https://portal.mardi4nfdi.de/)  
3. Bravo MaRDI: A Wikibase Powered Knowledge Graph on ... \- dblp, 7月 19, 2025にアクセス、 [https://dblp.org/rec/journals/corr/abs-2309-11484](https://dblp.org/rec/journals/corr/abs-2309-11484)  
4. Bravo MaRDI: A Wikibase Knowledge Graph on Mathematics \- Wikidata Workshop, 7月 19, 2025にアクセス、 [https://wikidataworkshop.github.io/2023/papers/15\_\_novel\_bravo\_mardi\_a\_wikibase\_%5B1%5D.pdf](https://wikidataworkshop.github.io/2023/papers/15__novel_bravo_mardi_a_wikibase_%5B1%5D.pdf)  
5. Wikibase, Wikidata, and Knowledge Graphs \- Professional Wiki, 7月 19, 2025にアクセス、 [https://professional.wiki/en/wikibase-wikidata-and-knowledge-graphs](https://professional.wiki/en/wikibase-wikidata-and-knowledge-graphs)  
6. OntoMathPRO: An Ontology of Mathematical Knowledge, 7月 19, 2025にアクセス、 [https://kpfu.ru/staff\_files/F2070552642/S1064562422700016.pdf](https://kpfu.ru/staff_files/F2070552642/S1064562422700016.pdf)  
7. New components of the OntoMathPRO ontology for representing math knowledge, 7月 19, 2025にアクセス、 [https://www.researchgate.net/publication/374853589\_New\_components\_of\_the\_OntoMathPRO\_ontology\_for\_representing\_math\_knowledge](https://www.researchgate.net/publication/374853589_New_components_of_the_OntoMathPRO_ontology_for_representing_math_knowledge)  
8. MaRDI Model Ontology classes and their relations. Visualisation done with Web-VOWL., 7月 19, 2025にアクセス、 [https://www.researchgate.net/figure/MaRDI-Model-Ontology-classes-and-their-relations-Visualisation-done-with-Web-VOWL\_fig3\_373794021](https://www.researchgate.net/figure/MaRDI-Model-Ontology-classes-and-their-relations-Visualisation-done-with-Web-VOWL_fig3_373794021)  
9. Algorithm Knowledge Graph Ontology, 7月 19, 2025にアクセス、 [https://algodata.mardi4nfdi.de/static/widoco/v1/index-en.html](https://algodata.mardi4nfdi.de/static/widoco/v1/index-en.html)  
10. Web Ontology Language \- Wikipedia, 7月 19, 2025にアクセス、 [https://en.wikipedia.org/wiki/Web\_Ontology\_Language](https://en.wikipedia.org/wiki/Web_Ontology_Language)  
11. The Mathematical Semantic Web \- CiteSeerX, 7月 19, 2025にアクセス、 [https://citeseerx.ist.psu.edu/document?repid=rep1\&type=pdf\&doi=8de81efaac59426eda2c9311c0db64d2c3e2120c](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=8de81efaac59426eda2c9311c0db64d2c3e2120c)  
12. Getting started with Apache Jena, 7月 19, 2025にアクセス、 [https://jena.apache.org/getting\_started/](https://jena.apache.org/getting_started/)  
13. Fuseki Quickstart \- Apache Jena, 7月 19, 2025にアクセス、 [https://jena.apache.org/documentation/fuseki2/fuseki-quick-start.html](https://jena.apache.org/documentation/fuseki2/fuseki-quick-start.html)  
14. Creating a Mathematical Knowledge Graph Using Lean 4's Mathlib ..., 7月 19, 2025にアクセス、 [https://epikprotocol.medium.com/creating-a-mathematical-knowledge-graph-using-lean-4s-mathlib-library-b187d1af663c](https://epikprotocol.medium.com/creating-a-mathematical-knowledge-graph-using-lean-4s-mathlib-library-b187d1af663c)  
15. RDF Triple Stores vs. Property Graphs: What's the Difference? \- Neo4j, 7月 19, 2025にアクセス、 [https://neo4j.com/blog/knowledge-graph/rdf-vs-property-graphs-knowledge-graphs/](https://neo4j.com/blog/knowledge-graph/rdf-vs-property-graphs-knowledge-graphs/)  
16. RDFLib and Neo4j \- Google Groups, 7月 19, 2025にアクセス、 [https://groups.google.com/g/rdflib-dev/c/y5CweAwtHGE](https://groups.google.com/g/rdflib-dev/c/y5CweAwtHGE)  
17. OMV \- Ontology Metadata Vocabulary, 7月 19, 2025にアクセス、 [https://oeg.fi.upm.es/index.php/en/downloads/75-omv/index.html](https://oeg.fi.upm.es/index.php/en/downloads/75-omv/index.html)  
18. Ontology Metadata Vocabulary \- NCBO BioPortal, 7月 19, 2025にアクセス、 [https://bioportal.bioontology.org/ontologies/OMV](https://bioportal.bioontology.org/ontologies/OMV)  
19. Project Basics – Quarto, 7月 19, 2025にアクセス、 [https://quarto.org/docs/projects/quarto-projects.html](https://quarto.org/docs/projects/quarto-projects.html)  
20. Cross References – Quarto, 7月 19, 2025にアクセス、 [https://quarto.org/docs/authoring/cross-references.html](https://quarto.org/docs/authoring/cross-references.html)  
21. Front Matter \- Quarto, 7月 19, 2025にアクセス、 [https://quarto.org/docs/authoring/front-matter.html](https://quarto.org/docs/authoring/front-matter.html)  
22. 8 Setting options with YAML \- Quarto: The Definitive Guide, 7月 19, 2025にアクセス、 [https://quarto-tdg.org/yaml.html](https://quarto-tdg.org/yaml.html)  
23. Python Frontmatter — Python Frontmatter 1.0.0 documentation, 7月 19, 2025にアクセス、 [https://python-frontmatter.readthedocs.io/](https://python-frontmatter.readthedocs.io/)  
24. python-frontmatter \- PyPI, 7月 19, 2025にアクセス、 [https://pypi.org/project/python-frontmatter/](https://pypi.org/project/python-frontmatter/)  
25. Generating Millions Of Lean Theorems With Proofs By Exploring State Transition Graphs, 7月 19, 2025にアクセス、 [https://arxiv.org/html/2503.04772v1](https://arxiv.org/html/2503.04772v1)  
26. Topic: Dependency Graph \- Zulip Chat Archive, 7月 19, 2025にアクセス、 [https://leanprover-community.github.io/archive/stream/113488-general/topic/Dependency.20Graph.html](https://leanprover-community.github.io/archive/stream/113488-general/topic/Dependency.20Graph.html)  
27. Getting Started — LeanDojo 4.20.0 documentation, 7月 19, 2025にアクセス、 [https://leandojo.readthedocs.io/en/latest/getting-started.html](https://leandojo.readthedocs.io/en/latest/getting-started.html)  
28. Apache Jena Fuseki, 7月 19, 2025にアクセス、 [https://jena.apache.org/documentation/fuseki2/](https://jena.apache.org/documentation/fuseki2/)  
29. Creating RESTful APIs Using SPARQL A Detailed and In-Depth Step-by-Step Tutorial for Developers \- MoldStud, 7月 19, 2025にアクセス、 [https://moldstud.com/articles/p-creating-restful-apis-using-sparql-a-detailed-and-in-depth-step-by-step-tutorial-for-developers](https://moldstud.com/articles/p-creating-restful-apis-using-sparql-a-detailed-and-in-depth-step-by-step-tutorial-for-developers)  
30. How to Use the SPARQL Endpoint \- PoolParty Semantic Suite Documentation, 7月 19, 2025にアクセス、 [https://help.poolparty.biz/en/developer-guide/basic---advanced-server-apis/poolparty-s-sparql-endpoint/how-to-use-the-sparql-endpoint.html](https://help.poolparty.biz/en/developer-guide/basic---advanced-server-apis/poolparty-s-sparql-endpoint/how-to-use-the-sparql-endpoint.html)  
31. Introduction to Neo4j & GraphQL | Development | Free Neo4j Courses from GraphAcademy, 7月 19, 2025にアクセス、 [https://graphacademy.neo4j.com/courses/graphql-basics/](https://graphacademy.neo4j.com/courses/graphql-basics/)  
32. Introduction \- Neo4j GraphQL Library, 7月 19, 2025にアクセス、 [https://neo4j.com/docs/graphql/current/](https://neo4j.com/docs/graphql/current/)  
33. Interactivity \- Quarto, 7月 19, 2025にアクセス、 [https://quarto.org/docs/interactive/](https://quarto.org/docs/interactive/)  
34. Observable JS \- Quarto, 7月 19, 2025にアクセス、 [https://quarto.org/docs/interactive/ojs/](https://quarto.org/docs/interactive/ojs/)  
35. D3 by Observable | The JavaScript library for bespoke data ..., 7月 19, 2025にアクセス、 [https://d3js.org/](https://d3js.org/)  
36. htmlwidgets for R \- Quarto, 7月 19, 2025にアクセス、 [https://quarto.org/docs/interactive/widgets/htmlwidgets.html](https://quarto.org/docs/interactive/widgets/htmlwidgets.html)  
37. Quarto Render · Actions · GitHub Marketplace · GitHub, 7月 19, 2025にアクセス、 [https://github.com/marketplace/actions/quarto-render](https://github.com/marketplace/actions/quarto-render)  
38. Publishing with Continuous Integration (CI) \- Quarto, 7月 19, 2025にアクセス、 [https://quarto.org/docs/publishing/ci.html](https://quarto.org/docs/publishing/ci.html)  
39. SKG-LLM: Developing a Mathematical Model for Stroke ... \- arXiv, 7月 19, 2025にアクセス、 [https://arxiv.org/abs/2503.06475](https://arxiv.org/abs/2503.06475)  
40. AI Semantic Credibility and Wikibase Knowledge Graph Self-Veriﬁcation \- iPRES 2024, 7月 19, 2025にアクセス、 [https://ipres2024.pubpub.org/pub/93xgtzp9](https://ipres2024.pubpub.org/pub/93xgtzp9)  
41. Graph-Augmented Reasoning: Evolving Step-by-Step ... \- arXiv, 7月 19, 2025にアクセス、 [https://arxiv.org/abs/2503.01642](https://arxiv.org/abs/2503.01642)
