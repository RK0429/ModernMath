# **A Bird's-Eye View of Modern Mathematics: From Foundations to the Frontier**

## **Part I: Foundations of Mathematics**

### **Part Introduction**

The magnificent edifice of mathematics is built upon an unshakable foundation. In this first part, we establish the language, logic, and fundamental objects that form the basis of all mathematical inquiry. We first explore mathematical logic, the tool for rigorously determining the truth of mathematical statements, and then learn set theory, the universal framework for handling collections of mathematical objects. Finally, using these tools, we rigorously construct the mathematical objects we are most familiar with: "numbers"—the number systems from natural numbers to complex numbers. These contents provide the common vocabulary and rules of inference used in all subsequent parts, the cornerstone of all mathematics [1]. Furthermore, we will touch on the basics of category theory, which embodies the structuralist perspective of modern mathematics, and prepare to capture the universal patterns that run through different mathematical fields.

### **Chapter 1: Logic and Sets**

#### **Section 1.1: Mathematical Logic**

Mathematical logic is the field that treats mathematical reasoning itself as an object of mathematical study. It clarifies the structure and limits of the process by which we arrive at certain conclusions.

##### **Subsection 1.1.1: Propositional and Predicate Logic**

Propositional logic is the most basic logical system that deals with the truth values of propositions connected by logical connectives such as "and," "or," and "if...then." Predicate logic, on the other hand, introduces quantifiers like "for all" and "there exists," allowing for the description of properties and relations of objects, thereby enabling the expression of richer mathematical statements. These are the first step towards formalizing the language of mathematics.

##### **Subsection 1.1.2: Structure of Proofs and Formal Systems**

We formally define what a "proof" is in mathematics. We introduce formal systems consisting of axioms (starting assumptions) and rules of inference (rules for deriving new theorems from axioms and known theorems) and see how proofs are constructed within them. This makes it possible to mechanically verify the correctness of a proof.

##### **Subsection 1.1.3: Introduction to Model Theory**

Model theory studies the relationship between formal languages (axiomatic systems) and the mathematical structures that interpret them (models). For example, it considers the correspondence between a formal description like "the axioms of a group" and concrete mathematical objects like "the additive group of integers" or "the multiplicative group of regular matrices." This perspective is a powerful tool for rigorously capturing analogies between different mathematical fields [2].

##### **Subsection 1.1.4: Completeness and Incompleteness Theorems**

Gödel's completeness theorem guarantees that in predicate logic, "every true proposition is provable." This is a fundamental result showing that our system of reasoning is logically sound. On the other hand, Gödel's incompleteness theorems show that any sufficiently powerful formal system containing arithmetic necessarily has "propositions whose truth value cannot be determined (independent propositions)." This delineates the limits of mathematical capability and had a profound impact on 20th-century mathematical and philosophical thought.

#### **Section 1.2: Set Theory**

Set theory provides the basic language for describing almost all areas of modern mathematics [2].

##### **Subsection 1.2.1: Axiomatic Set Theory - ZFC**

To avoid the paradoxes inherent in naive set theory (such as Russell's paradox), the ZFC axiom system, which adds the axiom of choice to the Zermelo-Fraenkel axioms, was introduced. This has become the de facto standard foundation for modern mathematics. Here, we learn about each of the ZFC axioms and their roles.

##### **Subsection 1.2.2: Ordinals and Cardinals**

Ordinals represent the order types of well-ordered sets and enable constructions and proofs by transfinite induction. Cardinals are a concept for measuring the "size" or "cardinality" of sets, classifying infinite sets by their size. The distinction between countable and uncountable infinity is essential in analysis and topology [2].

##### **Subsection 1.2.3: The Axiom of Choice and its Equivalents**

The axiom of choice, while intuitively obvious, leads to several non-intuitive theorems (such as the Banach-Tarski paradox). This axiom is known to be equivalent to propositions indispensable in many areas of modern mathematics, such as the existence of a basis for a vector space, the well-ordering theorem, and Zorn's lemma.

##### **Subsection 1.2.4: The Continuum Hypothesis and Modern Set Theory**

The continuum hypothesis is the problem of whether there exists an infinite set with a size "intermediate" between the set of natural numbers and the set of real numbers. The work of Gödel and Cohen showed that this hypothesis is an independent proposition that can neither be proved nor disproved from the ZFC axioms. This suggests that mathematical "truth" may not be singular and has led to modern set theory research exploring new axioms such as large cardinal axioms.

### **Chapter 2: Construction of Number Systems**

#### **Section 2.1: From Natural Numbers to Real Numbers**

We rigorously reconstruct the numbers used in daily life on the foundation of set theory and logic.

##### **Subsection 2.1.1: Peano Axioms and Natural Numbers**

We introduce the Peano axioms, which formalize the essential properties of natural numbers (the existence of 0, the successor function, and mathematical induction). This allows for the rigorous definition of arithmetic on natural numbers (addition, multiplication) and the proof of their properties [2].

##### **Subsection 2.1.2: Construction of Integers and Rational Numbers**

We construct integers (introducing negative numbers) as equivalence classes of pairs of natural numbers, and rational numbers (introducing fractions) as equivalence classes of pairs of integers. Through this process, we understand how larger number systems are algebraically constructed from existing ones.

##### **Subsection 2.1.3: Construction of Real Numbers: Dedekind Cuts and Cauchy Sequences**

There are "gaps" in the rational numbers (for example, the solution to x²=2 is not a rational number). To fill these gaps and achieve continuity, we construct the real numbers. Dedekind cuts are a construction focused on the order structure, while Cauchy sequences are a construction focused on the metric structure (convergence). Through these constructions, the axiom of completeness of the real numbers (the least upper bound property) is derived as a theorem.

#### **Section 2.2: Complex Numbers and Beyond**

We further extend the world of real numbers and explore number systems with algebraic richness and geometric breadth.

##### **Subsection 2.2.1: Algebraic and Geometric Introduction to Complex Numbers**

We introduce the imaginary unit i satisfying i²=−1 and adjoin it to the real numbers to construct the field of complex numbers. Complex numbers can be interpreted not only as algebraic expressions a+bi but also as points or vectors in the complex plane, and are deeply connected to geometric intuition (rotation and scaling) [2].

##### **Subsection 2.2.2: Quaternions, Octonions, and Algebraic Structures**

We further generalize the construction of complex numbers to introduce quaternions (Hamilton numbers) with a non-commutative product, and octonions (Cayley numbers) with a non-associative product. These number systems play important roles in describing rotations in 3D space and in modern physics, such as elementary particle theory. Through these, we see how the concept of number extends to more general algebraic structures such as fields, skew-fields, and non-associative algebras [2].

### **Chapter 3: Introduction to Mathematical Structures**

#### **Section 3.1: Algebraic Systems**

We focus not on individual objects, but on the rules of operations (structures) defined between them.

##### **Subsection 3.1.1: Definitions and Examples of Groups, Rings, and Fields**

We define the axioms of the basic building blocks of modern algebra: groups (describing symmetry), rings (generalizing the arithmetic of integers), and fields (systems where the four arithmetic operations are possible), and show that various mathematical objects such as integers, rational numbers, polynomials, and matrices possess these structures.

#### **Section 3.2: Order and Topological Structures**

We abstract concepts such as the greater/lesser relationship of numbers and the "closeness" of points.

##### **Subsection 3.2.1: Partial Orders and Lattices**

We define a partial order, a "greater/lesser relationship" where not all pairs are comparable. Examples include the inclusion relation of sets and the divisibility relation of integers. A lattice is a partially ordered set where any two elements have a least upper bound and a greatest lower bound, and it plays an important role in logic and computer science.

##### **Subsection 3.2.2: Introduction to Metric and Topological Spaces**

A metric space, which axiomatically defines the "distance" between points, is a natural stage for generalizing the concepts of limit and continuity in analysis. Furthermore, a topological space, which defines "closeness" and "connectedness" using only the concept of open sets, discarding the concept of distance, is a more flexible and powerful framework and forms the basis of modern geometry [3].

#### **Section 3.3: Category Theory: The Language of Structures**

We learn the basics of a very abstract and powerful theory that studies "structure" itself, which is common to various fields of modern mathematics. Introducing category theory at the foundational stage of mathematics may seem highly specialized at first glance, but in reality, it is the most effective approach to acquiring a unified perspective on modern mathematics. Concepts that appear in different fields, such as linear maps in linear algebra, homomorphisms in group theory, and continuous maps in topology, all share a common pattern of "structure-preserving maps (morphisms)." Category theory provides a language for rigorously describing such cross-disciplinary similarities [4]. This early introduction allows learners to be aware of the universal structures behind individual fields as they study them, and to understand mathematics as a whole as a deeply connected system rather than a collection of fragmented knowledge.

##### **Subsection 3.3.1: Categories, Functors, and Natural Transformations**

A category consists of a collection of objects and a collection of morphisms (arrows) between them. A functor is a "structure-preserving map" from one category to another, serving as a bridge between different mathematical fields. A natural transformation describes a "natural" transformation from one functor to another. These are the basic vocabulary of category theory.

##### **Subsection 3.3.2: Defining Objects via Universal Properties**

We learn the idea of "universality," which uniquely characterizes a specific object not by its internal structure, but by its relationship with all other objects (a pattern of morphisms). For example, the direct product of two sets is defined by the property that "a pair of maps from any set to those two sets induces a unique map to the direct product." This technique allows for the unified and elegant treatment of various constructions in algebra and topology.

##### **Subsection 3.3.3: Topos: A Category Connecting Logic and Geometry**

As a development of category theory, the topos, introduced by Grothendieck, is an extremely powerful concept that integrates and generalizes set theory and topology. A topos, while seemingly very abstract, is defined as a category that possesses many of the properties of the "category of sets." However, its internal logic is not necessarily classical logic (where the law of excluded middle holds) and can be intuitionistic logic. The most basic example is the category of sets itself, but a more important example is the "category of sheaves" Sh(X) on a topological space X. This can be seen as a collection of objects (sheaves) that associate a set F(U) to each open set U of X and can be "glued" together consistently. In this view, the space itself is not seen as a set of points, but is re-envisioned as the category of sheaves (topos) on it. This abstraction makes it possible to apply geometric intuition to fields like number theory, which is impossible in ordinary spaces (e.g., étale topos). Topos theory also has the potential to provide a foundation for mathematics in place of set theory and is a frontier of modern mathematics that unravels the profound relationship between logic and geometry.

## **Part II: The World of Algebra**

### **Part Introduction**

Algebra is a vast field of study that investigates symmetry, quantity, and structure. Its essence lies in moving away from concrete numbers and figures, abstracting the rules of operations using symbols, and exploring their purely logical consequences [2]. In this part, we begin with linear algebra, which is applied in every aspect of modern science and technology. Within the framework of vector spaces, we thoroughly analyze the most fundamental structure of linearity [3]. Next, we proceed to abstract algebra, which deals with more abstract structures—groups, rings, and fields. Groups are the mathematical expression of symmetry, while rings and fields generalize the operational rules of the world of numbers we are accustomed to [1]. We will then see how these abstract theories provide powerful weapons for the study of number theory, hailed as the "queen of mathematics." In particular, revealing that error-correcting codes, which support modern cryptography and information communication, are deeply rooted in the pure algebraic theories of finite fields and group theory will be a prime example of the practical power of abstraction [4].

### **Chapter 4: Linear Algebra**

Linear algebra deals with vectors and matrices, and studies systems of linear equations and linear transformations. Its applications are wide-ranging, including physics, statistics, computer science, and economics, and it is one of the most fundamental and powerful tools in modern mathematics [3].

#### **Section 4.1: Vector Spaces and Linear Maps**

##### **Subsection 4.1.1: Vector Spaces, Bases, and Dimension**

We learn the axioms of a vector space, a set where addition and scalar multiplication are defined. We introduce the concepts of linear independence, span, and basis, and show that any vector space has a well-defined dimension, an invariant that represents its "size" [3].

##### **Subsection 4.1.2: Linear Maps and their Matrix Representations**

We define a linear map as a map that preserves the structure between vector spaces. We see that by fixing a basis, any linear map can be represented by a matrix (its matrix representation). This translates abstract problems about maps into concrete computational problems with matrices.

#### **Section 4.2: Matrix Theory**

##### **Subsection 4.2.1: Determinants, Inverses, and Rank**

The determinant, defined for a square matrix, is a quantity that represents how much the corresponding linear transformation changes volume, and is used to determine whether a matrix is invertible (has an inverse). The rank of a matrix corresponds to the dimension of the image of the linear map and characterizes the existence of solutions to systems of linear equations.

##### **Subsection 4.2.2: Eigenvalues and Eigenvectors**

A special vector whose direction is unchanged by a linear transformation, only its magnitude being scaled, is called an eigenvector, and the scaling factor is called an eigenvalue. Eigenvalues and eigenvectors capture the essential "characteristics" of a linear transformation and are extremely important in applications such as stability analysis of dynamical systems and data analysis (principal component analysis) [3].

##### **Subsection 4.2.3: Diagonalization and Jordan Normal Form**

Many important matrices can be transformed into a very simple form, a diagonal matrix, by choosing their eigenvectors as a basis (diagonalization). Even if diagonalization is not possible, any matrix can always be transformed into a form close to a diagonal matrix, called the Jordan normal form. This is the pinnacle of the theory of standard forms for completely understanding the structure of linear transformations [7].

#### **Section 4.3: Inner Product Spaces**

We introduce an inner product structure into a vector space to measure the "length" and "angle" of vectors.

##### **Subsection 4.3.1: Inner Products, Norms, and Orthogonality**

We define the axioms of an inner product and introduce the concepts of norm (length) and distance that are naturally determined from the inner product. When the inner product of two vectors is 0, they are said to be orthogonal. The Gram-Schmidt process allows any basis to be converted into an orthonormal basis.

##### **Subsection 4.3.2: Normal Matrices and the Spectral Theorem**

A normal matrix, a broader class that includes Hermitian and unitary matrices, can always be diagonalized by a unitary matrix. This spectral theorem plays a central role in applications to physics, such as the theory of observables in quantum mechanics.

#### **Section 4.4: Multilinear Algebra**

We deal with linear maps that take multiple vectors as variables.

##### **Subsection 4.4.1: Dual Spaces and Tensor Products**

The space of all linear maps (linear functionals) from a vector space to its field of coefficients is called the dual space. The tensor product is a universal way to construct a new vector space from two vector spaces and is indispensable for tensor analysis in relativity and the description of many-body systems in quantum mechanics.

### **Chapter 5: Abstract Algebra: Groups, Rings, and Fields**

We move away from concrete numerical calculations and explore the rules of operations axiomatically.

#### **Section 5.1: Group Theory**

A group is a mathematical structure that describes "symmetry."

##### **Subsection 5.1.1: Definitions, Subgroups, and Homomorphisms**

We define the axioms of a group (associativity, existence of an identity element, existence of an inverse element) and consider various examples such as the additive group of integers, permutation groups, and symmetry transformation groups of figures. We learn about subgroups, which are the internal structure of a group, and homomorphisms, which are maps that preserve the structure between two groups [8].

##### **Subsection 5.1.2: Lagrange's Theorem and Cosets**

In a finite group, the order of a subgroup is always a divisor of the order of the original group. This Lagrange's theorem is the most fundamental result in the study of the structure of finite groups. Its proof uses the concept of cosets, which classify the group by its subgroups.

##### **Subsection 5.1.3: Sylow's Theorems and the Structure of Finite Groups**

Sylow's theorems partially guarantee the converse of Lagrange's theorem, providing strong information about the existence and number of specific subgroups (Sylow p-subgroups) from the order of a finite group. This has greatly advanced the research of classifying finite groups of a given order [9].

##### **Subsection 5.1.4: The Classification of Finite Simple Groups: An Overview**

Finite simple groups, which are "atomic" groups that cannot be broken down further, were completely classified through a massive collaborative effort by mathematicians in the latter half of the 20th century. This "periodic table of mathematics" consists of cyclic groups, alternating groups, groups of Lie type, and 26 sporadic simple groups. This classification theorem is one of the pinnacles of modern algebra [10].

#### **Section 5.2: Ring Theory**

A ring is an algebraic system with two operations, addition and multiplication, and is a generalization of the arithmetic of integers.

##### **Subsection 5.2.1: Rings, Ideals, and Homomorphisms**

We define the axioms of a ring and give examples such as the ring of integers, polynomial rings, and matrix rings. The important concept corresponding to subgroups in ring theory is the ideal, which is used to construct quotient rings. A map that preserves the structure between rings is a ring homomorphism [8].

##### **Subsection 5.2.2: Prime and Maximal Ideals**

The concept corresponding to prime numbers in number theory is the prime ideal, which is linked to the concept of points in algebraic geometry. Prime and maximal ideals play a central role in investigating the structure of rings.

##### **Subsection 5.2.3: Euclidean, Principal Ideal, and Unique Factorization Domains**

A unique factorization domain (UFD) is a generalization of a ring where "uniqueness of prime factorization" holds, like the ring of integers. A principal ideal domain (PID), where every ideal is generated by a single element, is a UFD, and a Euclidean domain, where the Euclidean algorithm can be applied, is a PID. We learn the relationships between these classes of rings [9].

##### **Subsection 5.2.4: Introduction to Commutative Algebra: Noetherian Rings and Hilbert's Basis Theorem**

Commutative algebra developed as the language of algebraic geometry. A Noetherian ring, in which any ideal is finitely generated, is a particularly important class among them. Hilbert's basis theorem, which guarantees that "a polynomial ring over a Noetherian ring is again a Noetherian ring," is a powerful theorem that forms the basis of algebraic geometry.

#### **Section 5.3: Field Theory and Galois Theory**

A field is an algebraic system where the four arithmetic operations can be freely performed, and Galois theory is a beautiful theory that connects field extensions and group theory.

##### **Subsection 5.3.1: Field Extensions**

A larger field containing a certain field is called an extension field of the original field. We learn about the degree of the extension and the algebraic properties of the original field (algebraic extension, transcendental extension).

##### **Subsection 5.3.2: Galois Groups and the Galois Correspondence**

We associate a Galois group, which is its automorphism group, to a field extension. The fundamental theorem of Galois theory shows that there is a beautiful one-to-one correspondence (the Galois correspondence) between the intermediate fields of the extension field and the subgroups of the Galois group. This translates problems about fields into problems about finite groups [8].

##### **Subsection 5.3.3: Solvability of Equations by Radicals**

As a classical application of Galois theory, there is the proof that there is no "solution formula using radicals" for general algebraic equations of degree 5 or higher. This is reduced to the group-theoretic property of whether the Galois group corresponding to the equation is a solvable group.

##### **Subsection 5.3.4: Finite Fields and their Applications**

We investigate the structure of fields with a finite number of elements, namely finite fields (Galois fields). The theory of finite fields is not only an object of pure mathematics but also a foundation that supports modern technology. For example, Reed-Solomon codes, one of the error-correcting codes used in QR codes, CDs, and DVDs, are designed based on polynomial operations over finite fields [11]. Also, in modern cryptographic theory such as public-key cryptography, the structure of finite fields, especially the properties of their multiplicative groups, is the basis for security [4]. Thus, the way abstract algebraic theory is directly connected to solving real-world problems is one of the major features of modern mathematics.

### **Chapter 6: Number Theory: The Science of Integers**

"Mathematics is the queen of the sciences, and number theory is the queen of mathematics," are the words of Gauss. Number theory studies integers, which are the most basic yet hold the most profound mysteries.

#### **Section 6.1: Elementary Number Theory**

We explore the properties of integers without using advanced tools from algebra or analysis.

##### **Subsection 6.1.1: Divisibility, Congruences, and the Chinese Remainder Theorem**

We learn the basics of divisibility, such as the calculation of the greatest common divisor by the Euclidean algorithm and the uniqueness of prime factorization (the fundamental theorem of arithmetic). Congruence, which focuses on the remainder when a number is divided by a modulus, is a powerful language in number theory. The Chinese Remainder Theorem guarantees the existence and uniqueness of solutions to systems of linear congruences [14].

##### **Subsection 6.1.2: Fermat's Little Theorem and Euler's Theorem**

Fermat's little theorem is a fundamental result concerning congruences modulo a prime number, and Euler's theorem is its generalization. These theorems are the basis of modern cryptography such as RSA encryption [15].

##### **Subsection 6.1.3: The Law of Quadratic Reciprocity**

The problem of whether an integer is a quadratic residue modulo a prime (i.e., a perfect square) shows a surprising symmetry between the questions for two different primes p and q. This law of quadratic reciprocity, proved by Gauss, is considered the pinnacle of elementary number theory [14].

#### **Section 6.2: Algebraic Number Theory**

We study numbers that are solutions to algebraic equations and explore the properties of integers deeply using the tools of abstract algebra.

##### **Subsection 6.2.1: Number Fields and Rings of Integers**

We define an algebraic number field, which is a finite extension of the rational numbers, and consider the set of all algebraic integers (a generalization of "integers") contained within it (the ring of integers). For example, the Gaussian integers a+bi (where a, b are integers) are an example [16].

##### **Subsection 6.2.2: Unique Factorization of Ideals**

In the ring of integers of an algebraic number field, the uniqueness of prime factorization does not necessarily hold. However, as shown by Dedekind, by considering ideals instead of individual numbers, the beautiful property of "unique factorization into prime ideals" is restored. This is a fundamental result of algebraic number theory [18].

##### **Subsection 6.2.3: Class Groups and Unit Groups**

The ideal class group is an indicator that measures the extent to which the uniqueness of prime ideal factorization fails, and its order (the class number) being 1 is equivalent to unique factorization. The unit group is the group of invertible elements in the ring of integers, and its structure is revealed by Dirichlet's unit theorem. These are the most basic invariants of an algebraic number field [16].

##### **Subsection 6.2.4: Local Fields and p-adic Numbers**

To investigate properties related to a specific prime p, we introduce the p-adic number field (a local field), which is a completion of the rational numbers in a different way from the real numbers. As represented by Hensel's lemma, algebraic equations are often easier to handle in the world of p-adic numbers, enabling a powerful approach of "deriving global properties from local properties" (the local-global principle) [18].

#### **Section 6.3: Analytic Number Theory**

We use methods from analysis, such as calculus and complex analysis, to study the collective properties of integers, such as the distribution of prime numbers.

##### **Subsection 6.3.1: The Prime Number Theorem**

The prime number theorem, which states that the number of primes less than or equal to x, π(x), is asymptotic to x/ln(x) as x becomes large, is a central result of analytic number theory that captures the global distribution of primes [20].

##### **Subsection 6.3.2: The Riemann Zeta Function and L-Functions**

The Riemann zeta function ζ(s)=∑n=1∞ n⁻ˢ is a surprising bridge that translates the properties of prime numbers into the properties of a complex analytic function. The Riemann hypothesis concerning the distribution of its zeros is the most important and difficult unsolved problem in mathematics. Dirichlet's L-functions, which generalize the zeta function, were introduced to study primes in arithmetic progressions [22].

##### **Subsection 6.3.3: Dirichlet's Theorem on Primes in Arithmetic Progressions**

Given two coprime integers a and m, the arithmetic progression a, a+m, a+2m, ... contains infinitely many prime numbers. This theorem was proved using the properties of L-functions and showed how powerful analytic methods are for purely number-theoretic problems [20].

##### **Subsection 6.3.4: Additive Number Theory: Goldbach's Conjecture and Waring's Problem**

We study the problem of representing an integer as a sum of other integers, i.e., the additive structure of integers. For example, Goldbach's conjecture, which states that "every even integer greater than 2 is the sum of two primes," and Waring's problem, which states that "every natural number is the sum of at most g(k) k-th powers" (solved by Hilbert), belong to this field [22].

### **Chapter 7: Advanced Topics in Algebra**

#### **Section 7.1: Representation Theory**

A field that studies the structure of groups in the language of linear algebra by "representing" abstract groups as groups of more concrete linear transformations (matrices).

##### **Subsection 7.1.1: Representations of Finite Groups**

The representations of a finite group over the field of complex numbers can be completely decomposed into basic components called irreducible representations. Character theory is a powerful tool that investigates representations not by the matrices themselves, but by their traces, the characters.

##### **Subsection 7.1.2: Representations of Lie Groups and Lie Algebras**

A Lie group is a group that also has the structure of a manifold and describes continuous symmetries. Its representation theory plays a central role in the standard model of particle physics and other areas. A Lie algebra is a vector space that captures the infinitesimal structure of a Lie group, and its representation theory is closely related to the representation theory of Lie groups.

#### **Section 7.2: Homological Algebra**

A field that studies sequences of algebraic objects (complexes) and extracts deeper invariants of the original objects by investigating their "homology."

##### **Subsection 7.2.1: Chain Complexes and Homology**

A sequence of modules (or vector spaces) and a sequence of homomorphisms connecting them such that the composition of two consecutive maps is zero is called a chain complex. Its homology groups are an indicator that measures the extent to which this sequence is not "exact."

##### **Subsection 7.2.2: Ext and Tor Functors**

As a type of derived functor, which are basic tools of homological algebra, the Ext functor is used to classify extensions of groups, and the Tor functor is used to classify the properties of tensor products. They are widely applied in algebraic topology and algebraic geometry.

#### **Section 7.3: Algebraic Geometry**

A field that studies geometric figures (algebraic varieties) defined as the solutions of systems of polynomial equations, using the tools of algebra.

##### **Subsection 7.3.1: Affine and Projective Varieties**

We define affine varieties, which are algebraic varieties in Euclidean space, and projective varieties, which have better properties by adding points at infinity. Hilbert's Nullstellensatz gives a fundamental correspondence between the geometric properties of a variety and the algebraic properties of the polynomial ideal that defines it [4].

##### **Subsection 7.3.2: Sheaves: Gluing Local Data**

A sheaf is one of the most fundamental tools in modern geometry, especially in algebraic geometry and complex manifold theory. It is a framework for systematically handling "locally defined data" on a space and describing how they are "glued together" to form global data. For example, continuous functions, differentiable functions, and vector fields on a manifold can all be treated uniformly using the concept of a sheaf. The theory of sheaves is defined as associating some algebraic object (set, group, ring, etc.) to each open set of a space and satisfying consistency conditions called restriction maps and the "gluing axiom." This framework becomes the basis for the theory of schemes described next.

##### **Subsection 7.3.3: Introduction to Scheme Theory**

The concept of a scheme, introduced by Grothendieck, greatly generalizes algebraic varieties and allows for the treatment of number theory and geometry from a unified perspective. A scheme is a topological space with a sheaf of rings called the "structure sheaf" attached to it, which allows for the study of objects far beyond the framework of classical geometry, such as considering the ring of integers Spec(Z) as a kind of "one-dimensional figure" [28].

##### **Subsection 7.3.4: Geometry of Curves and Surfaces**

The classification theory of algebraic curves (one-dimensional varieties), especially the Riemann-Roch theorem, and algebraic surfaces (two-dimensional varieties), such as K3 surfaces, are rich and concrete research subjects in algebraic geometry [4].

##### **Subsection 7.3.5: Modern Trends: Motives, Derived Categories**

Motive theory is Grothendieck's grand vision to unify different cohomology theories (de Rham, Betti, étale). The derived category is a categorical refinement of homological algebra and is attracting attention as a powerful tool for studying invariants of algebraic varieties, especially in the context of mirror symmetry [4].

## **Part III: The World of Analysis**

### **Part Introduction**

Analysis is a vast area of mathematics that deals with limits, continuity, and change. Its starting point is the reconstruction of the calculus learned intuitively in high school on the rigorous logical system of the ε-δ method [28]. On this rigorous foundation, we expand the stage of analysis from the real number line to the complex plane, and further to infinite-dimensional function spaces where entire functions form a single point. In this part, we explore the wide-ranging influence of analysis, which has spread to every corner of modern science and technology, from the theory of differential equations, the basic language for describing physical phenomena, to Fourier analysis, the mathematical foundation of signal processing, image analysis, and quantum mechanics, and to measure theory and stochastic differential equations, the basis of modern probability theory and financial engineering. The study of analysis is not just about proving abstract theorems, but a grand narrative that shows how its theory becomes a powerful toolkit for modeling and analyzing the continuous phenomena of the real world and the discrete data of the digital world.

### **Chapter 8: Calculus**

#### **Section 8.1: Limits and Continuity**

We rigorously formalize the idea of "approaching," which is the basis of all concepts in analysis.

##### **Subsection 8.1.1: Convergence of Sequences and Series**

We define what it means for an infinite sequence of numbers to "converge" to a specific value using the ε-N definition. We also learn various methods for determining the convergence or divergence of infinite series, where an infinite number of terms are added together (d'Alembert's ratio test, Cauchy's root test, etc.).

##### **Subsection 8.1.2: Limits of Functions and the Epsilon-Delta Definition**

We rigorously define the limit of a function, which describes how the value of a function behaves as its variable approaches a specific value, using the ε-δ definition. This is the most fundamental concept in analysis and the basis for the definitions of differentiation and integration [29].

##### **Subsection 8.1.3: Properties of Continuous Functions (Intermediate Value Theorem, Extreme Value Theorem)**

We define a continuous function, which has the intuitive property that its graph is "connected." We prove that a continuous function defined on a closed interval has important properties for applications, such as the intermediate value theorem (it takes on all intermediate values) and the extreme value theorem (it always has a maximum and a minimum value).

#### **Section 8.2: Differentiation of Single-Variable Functions**

##### **Subsection 8.2.1: Derivatives and Differentiability**

We define the derivative, which represents the local rate of change of a function, i.e., the slope of the tangent to its graph, using limits. Differentiability means that a function can be well approximated by a straight line locally.

##### **Subsection 8.2.2: Mean Value Theorem and Taylor's Theorem**

The mean value theorem, which guarantees the existence of an instantaneous rate of change (derivative) equal to the average rate of change over an interval, is a fundamental theorem of calculus. Taylor's theorem, which approximates a sufficiently smooth function by a polynomial using the values of its derivatives at that point, is one of the most powerful tools for investigating the local behavior of functions [29].

#### **Section 8.3: Integration of Single-Variable Functions**

##### **Subsection 8.3.1: The Riemann Integral and Antiderivatives**

We define the area of the region enclosed by a graph and the x-axis as the limit of the sum of the areas of rectangles (the Riemann integral). On the other hand, the indefinite integral (antiderivative) is the operation of finding a function whose derivative is the original function.

##### **Subsection 8.3.2: The Fundamental Theorem of Calculus**

This theorem, which is at the pinnacle of calculus, shows that differentiation and integration, which seem unrelated at first glance, are in fact inverse operations of each other. This reduces the calculation of areas and volumes to the algebraic calculation of finding antiderivatives.

##### **Subsection 8.3.3: Improper Integrals**

We define the integral for cases where the interval of integration is infinite or the integrand is not bounded in the interval, using a limit operation. The Gaussian integral is an important example [29].

#### **Section 8.4: Multivariable Calculus**

We extend functions and their variables from one dimension to higher dimensions.

##### **Subsection 8.4.1: Partial and Total Derivatives**

In a multivariable function, the operation of differentiating with respect to only one variable is the partial derivative. The total derivative is a concept that gives the local linear approximation of a function and correctly captures the differentiability of a multivariable function.

##### **Subsection 8.4.2: Multiple Integrals and Change of Variables (Jacobians)**

We define multiple integrals such as double and triple integrals and apply them to the calculation of volumes and masses. The "distortion of the volume element" when changing the integration variables is described by the determinant made from the partial derivatives (the Jacobian) [29].

##### **Subsection 8.4.3: Vector Calculus: Gradient, Divergence, and Curl**

We describe scalar fields (such as temperature distribution) and vector fields (such as the velocity field of a flow) and introduce the differential operators gradient (grad), divergence (div), and curl (rot) to capture their spatial changes. These become the basic language of electromagnetism and fluid dynamics [3].

##### **Subsection 8.4.4: Line/Surface Integrals and the Integral Theorems of Green, Stokes, and Gauss**

We define line and surface integrals, which integrate a field along a curve or surface. Green's theorem, Stokes' theorem, and Gauss's divergence theorem are the fundamental theorems of vector calculus that connect "the integral of the derivative of a field inside a region" and "the integral of the field on the boundary of the region" in different dimensions, respectively [28].

### **Chapter 9: Real Analysis**

#### **Section 9.1: Measure Theory and Lebesgue Integration**

We overcome the limitations of the Riemann integral and construct a more powerful and theoretically superior theory of integration.

##### **Subsection 9.1.1: Measurable Sets and Lebesgue Measure**

We rigorously generalize the concepts of length, area, and volume to define "measure." In particular, the Lebesgue measure on Euclidean space can consistently determine the "size" of very complex figures [8].

##### **Subsection 9.1.2: Measurable Functions and the Lebesgue Integral**

Whereas the Riemann integral divides the domain, the Lebesgue integral defines the integral by dividing the range. This allows the integral to be defined for a broader class of functions (measurable functions) and makes it much more compatible with limit operations [3].

##### **Subsection 9.1.3: Convergence Theorems (Monotone Convergence, Dominated Convergence) and Fubini's Theorem**

One of the greatest advantages of the Lebesgue integral is the existence of powerful convergence theorems. The monotone convergence theorem and Lebesgue's dominated convergence theorem provide conditions that guarantee the interchange of the order of "the limit of the integral" and "the integral of the limit," and are powerful in various situations in analysis. Fubini's theorem gives conditions for rewriting a multiple integral as an iterated integral [3].

#### **Section 9.2: L^p Spaces**

We study the vector space of all Lebesgue integrable functions.

##### **Subsection 9.2.1: Norms and Completeness**

We introduce the Lp norm, defined as the 1/p power of the integral of the p-th power of the absolute value of a function. With respect to this norm, the Lp space is complete (any Cauchy sequence converges) and is an important example of a Banach space.

##### **Subsection 9.2.2: Hölder's and Minkowski's Inequalities**

Hölder's inequality is a fundamental inequality that bounds the integral of the product of two functions by the Lp norms of the respective functions. Minkowski's inequality shows that the Lp norm satisfies the triangle inequality, which guarantees that it is truly a norm.

### **Chapter 10: Complex Analysis**

We deal with functions of a complex variable. A beautiful, rigid theoretical system unfolds, remarkably different from real analysis.

#### **Section 10.1: Holomorphic Functions**

##### **Subsection 10.1.1: Complex Differentiation and the Cauchy-Riemann Equations**

The condition for a complex function to be complex differentiable (holomorphic) is much stronger than the condition for a real multivariable function to be totally differentiable, and requires that its real and imaginary parts satisfy a pair of partial differential equations called the Cauchy-Riemann equations [30].

##### **Subsection 10.1.2: Conformal Mappings**

A holomorphic function defines a map (a conformal map) that preserves the shape of infinitesimal figures and preserves angles. This property is applied to solving two-dimensional potential problems in fluid dynamics and electromagnetism, among other things [30].

#### **Section 10.2: Complex Integration**

##### **Subsection 10.2.1: Cauchy's Integral Theorem and Formula**

When a holomorphic function is integrated along a closed curve, its value is always 0 (Cauchy's integral theorem). This is the most fundamental and surprising result in complex analysis. Furthermore, Cauchy's integral formula shows that the value of a function at any point inside a region can be completely determined by the integral values on the boundary. This leads to the conclusion that holomorphic functions have strong properties, such as being infinitely differentiable [8].

##### **Subsection 10.2.2: Laurent Series and the Residue Theorem**

Around a singularity, a holomorphic function is expanded into a Laurent series, which also includes terms with negative powers. The residue theorem is a powerful theorem that shows that the integral of a function around a singularity can be calculated only by a specific coefficient of the Laurent expansion (the residue), and is widely applied to the calculation of definite integrals of real functions, among other things [3].

#### **Section 10.3: Global Properties of Holomorphic Functions**

##### **Subsection 10.3.1: Analytic Continuation and the Identity Theorem**

Analytic continuation is the operation of "naturally" extending a holomorphic function defined in a certain region to outside its domain of definition. The identity theorem shows that two holomorphic functions that agree on a small region agree on their entire domain of definition, which speaks to the strong rigidity of holomorphic functions [30].

##### **Subsection 10.3.2: Riemann Surfaces**

A Riemann surface is a stage where multi-valued functions like the logarithm function and the power root function can be naturally defined as single-valued functions. It is a one-dimensional complex manifold with a structure like multiple sheets of the complex plane glued together, and is an important concept deeply related to algebraic geometry and number theory [30].

### **Chapter 11: Functional Analysis**

A field that studies infinite-dimensional vector spaces of functions, fusing linear algebra and analysis.

#### **Section 11.1: Banach and Hilbert Spaces**

##### **Subsection 11.1.1: Normed and Banach Spaces**

A vector space with a norm (length) defined on it is called a normed space, and a complete one is called a Banach space. Lp spaces and spaces of continuous functions are typical examples [3].

##### **Subsection 11.1.2: Inner Product and Hilbert Spaces**

A Banach space with an inner product defined on it is called an inner product space, and a complete one is called a Hilbert space. A Hilbert space can be regarded as an infinite-dimensional version of Euclidean space, and geometric intuition works well. The mathematical formulation of quantum mechanics is done on a Hilbert space [3].

#### **Section 11.2: Linear Operators**

We study linear operators, which are linear maps between function spaces.

##### **Subsection 11.2.1: Bounded Linear Operators and Operator Norms**

A linear operator between normed spaces that maps bounded sets to bounded sets is called a bounded linear operator. This is equivalent to the operator being "continuous," and its "size" can be measured by the operator norm.

##### **Subsection 11.2.2: The Three Fundamental Theorems: Hahn-Banach, Open Mapping, Closed Graph**

The Hahn-Banach theorem guarantees the extendability of linear functionals, and the open mapping theorem and the closed graph theorem clarify the basic properties of continuous linear operators on Banach spaces. These form the backbone of the theory of functional analysis.

##### **Subsection 11.2.3: Spectral Theory**

We generalize the eigenvalue theory of finite dimensions to infinite-dimensional operators. The spectrum of an operator is the set of complex numbers for which the operator is not invertible, and it deeply reflects the properties of the operator. In particular, the spectral theory of self-adjoint operators on a Hilbert space is indispensable for the formulation of quantum mechanics.

#### **Section 11.3: Fourier Analysis and Distributions**

##### **Subsection 11.3.1: Fourier Series and Transforms**

We represent a periodic function as an infinite sum of trigonometric functions (a Fourier series) and a non-periodic function as a superposition of waves of various frequencies (a Fourier transform). This allows a function to be transformed from the time domain to the frequency domain, and its frequency components to be analyzed [3].

##### **Subsection 11.3.2: Theory of Distributions (Schwartz Functions)**

The theory of distributions is a theory that mathematically justifies "idealized functions" that are useful in physics, such as the delta function, but cannot be defined as ordinary functions. This greatly expands the tools of analysis, such as defining the derivative for non-differentiable functions [3].

##### **Subsection 11.3.3: Application: Signal and Image Processing**

Fourier analysis plays a central role in modern digital technology. Its applications are too numerous to count, including the analysis and noise reduction of audio signals, the design of communication systems, and the compression (JPEG, etc.) and filtering (blurring, sharpening) of images, and the reconstruction of medical images (MRI, CT) [33]. The Fourier transform is a powerful mathematical tool for extracting and processing hidden periodicities and features in data by converting time or space information into frequency information.

### **Chapter 12: Theory of Differential Equations**

Differential equations, which are relational expressions between an unknown function and its derivatives, are the basic language for describing phenomena in the natural sciences and engineering.

#### **Section 12.1: Ordinary Differential Equations**

We deal with differential equations concerning an unknown function of one variable.

##### **Subsection 12.1.1: Existence and Uniqueness of Solutions**

We discuss under what conditions a solution to a differential equation exists and is uniquely determined for an initial condition. The Picard-Lindelöf theorem (or the Cauchy-Lipschitz theorem) is its basic result [3].

##### **Subsection 12.1.2: Linear ODEs**

We learn the solution methods for linear ordinary differential equations, where the principle of superposition of solutions holds. In the case of constant coefficients, they can be solved exactly using the characteristic equation.

##### **Subsection 12.1.3: Dynamical Systems and Stability Theory**

We study the long-term behavior of the solutions of differential equations. We investigate the trajectories, equilibrium points, and periodic orbits of the solutions, and analyze their stability (response to perturbations) using methods such as Lyapunov functions [2].

#### **Section 12.2: Partial Differential Equations**

We deal with differential equations concerning an unknown function of multiple variables.

##### **Subsection 12.2.1: The Three Fundamental Equations: Heat, Wave, Laplace**

We learn the properties and solution methods (separation of variables, Fourier transform method, etc.) of the most basic partial differential equations that appear in physics: the heat equation, which describes the diffusion of heat; the wave equation, which describes vibrations and the propagation of waves; and the Laplace equation, which describes the potential in a steady state [3].

##### **Subsection 12.2.2: Sobolev Spaces and Weak Solutions**

We introduce the concept of a "weak solution," which allows functions that are not differentiable in the classical sense to be solutions. As a function space for this, Sobolev spaces, which consist of functions whose derivatives belong to Lp spaces, are used. This is the standard framework of modern partial differential equation theory.

##### **Subsection 12.2.3: Modern Topics: Nonlinear PDEs, Equations of Fluid Dynamics**

We go beyond the theory of linear equations and touch on the world of nonlinear partial differential equations that describe complex real-world phenomena. In particular, the Navier-Stokes equations, which describe the motion of fluids, are one of the most challenging research subjects in modern mathematics, with the problem of the existence and smoothness of their solutions remaining as one of the Millennium Prize Problems [39].

#### **Section 12.3: Stochastic Differential Equations**

We deal with differential equations that include a random noise term.

##### **Subsection 12.3.1: Brownian Motion and Itō Calculus**

We mathematically define Brownian motion (the Wiener process), which models the irregular motion of particles. Itō calculus is what makes it possible to integrate irregular processes like Brownian motion, which cannot be handled by ordinary integration theory.

##### **Subsection 12.3.2: Itō's Lemma and its Applications**

The chain rule (the rule for differentiating a composite function) for Itō calculus is Itō's formula. This corresponds to the fundamental theorem of calculus in stochastic analysis and is an indispensable tool for solving stochastic differential equations and investigating their properties [40]. In particular, it plays a central role in the derivation of the Black-Scholes equation in mathematical finance [4].

## **Part IV: The World of Geometry**

### **Part Introduction**

Geometry is one of the oldest and most intuitive fields of mathematics, exploring figures, spaces, and their invariant properties under transformation. Its exploration began with the axiomatic systematization of Euclidean geometry in ancient Greece and has developed into a grand theory in modern mathematics that fundamentally questions and extends our concept of space. The core of this part is the concept of a "manifold." A manifold is an extremely powerful and flexible framework for describing spaces that locally look like the Euclidean space we are familiar with, but globally can be complexly "curved" like the surface of a sphere or a donut, or "connected" in complex ways [8]. In this part, we will focus on the two major trends of modern geometry: differential geometry and topology. Differential geometry uses the tools of calculus to precisely measure the local properties of a manifold, such as its "curvature" [41]. On the other hand, topology studies the global properties that are unchanged by continuous deformations (stretching or shrinking, but not cutting or pasting), such as the number of holes [26]. These theories have become the language for describing the fundamental laws of physics, such as general relativity, or, as in topological data analysis, the abstract tools of pure mathematics are applied to cutting-edge data science, symbolizing the dynamism of modern mathematics.

### **Chapter 13: Foundations of Geometry**

#### **Section 13.1: Axiomatic Geometry**

##### **Subsection 13.1.1: Euclidean Geometry and the Parallel Postulate**

We learn the axiomatic system concerning points, lines, and circles, systematized by Euclid in his "Elements." In particular, the parallel postulate, which states that "through a point not on a given line, there is exactly one line parallel to the given line," is known for the failure of long-standing attempts to prove it from the other axioms.

##### **Subsection 13.1.2: Non-Euclidean Geometries: Hyperbolic and Spherical**

We see that by denying the parallel postulate, new, self-consistent geometric systems are born. Spherical geometry (where no parallel lines exist) and hyperbolic geometry (where infinitely many parallel lines exist) showed that Euclidean geometry is not the only geometry, and fundamentally transformed the concept of space [1].

#### **Section 13.2: Projective and Affine Geometry**

We learn about geometries obtained by removing or adding specific structures to Euclidean geometry. Projective geometry introduces the idea that parallel lines meet at a point at infinity, thereby mathematically formalizing the principles of perspective and drawing. Affine geometry is a geometry that discards the concepts of length and angle, and takes only parallelism as an axiom [26].

### **Chapter 14: Manifold Theory**

We introduce and investigate the properties of manifolds, the central research object of modern geometry.

#### **Section 14.1: Differentiable Manifolds**

##### **Subsection 14.1.1: Definition and Examples of Manifolds**

An n-dimensional manifold is a topological space that is locally homeomorphic to n-dimensional Euclidean space Rn. We rigorously define this concept using coordinate neighborhoods (charts) and coordinate transformations (atlases). The circle, sphere, and torus are familiar examples. When the coordinate transformations are smooth, it is called a differentiable manifold [8].

##### **Subsection 14.1.2: Tangent Spaces and Tangent Bundles**

At each point on a manifold, we define the tangent space as the set of all vectors that are "tangent" to that point. This can be interpreted as the space where velocity vectors and force vectors on the manifold live. The tangent bundle is what you get when you bundle together the tangent spaces of all points.

##### **Subsection 14.1.3: Vector Fields and Differential Forms**

A vector field associates a tangent vector to each point of a manifold and represents flows and forces. A differential form is a tool for measuring infinitesimal volume elements and area elements at each point, and its integral is related to the derivative of a higher-order form by Stokes' theorem [8].

#### **Section 14.2: Riemannian Geometry**

A geometry in which a differentiable manifold is equipped with an inner product (a Riemannian metric) on the tangent space at each point, allowing for the measurement of length, angle, area, and volume.

##### **Subsection 14.2.1: Riemannian Metrics and Geodesics**

We introduce a Riemannian metric and use it to define the length of a curve. A geodesic, which is the shortest path between two points, is a generalization of a straight line in Euclidean space.

##### **Subsection 14.2.2: Connections and Covariant Derivatives**

A connection is a concept for "parallel transporting" a vector field on a curved space, and the operation of differentiating a vector field using it is the covariant derivative. This allows the ordinary derivative in Euclidean space to be generalized to a manifold.

##### **Subsection 14.2.3: Curvature: Riemann Curvature Tensor, Sectional Curvature**

Curvature is a central concept that quantitatively expresses how much a space is "curved." The Riemann curvature tensor measures the discrepancy when a vector is parallel transported along different paths. The sectional curvature represents the curvature in a two-dimensional direction at each point and determines the overall geometric properties of the space [41].

#### **Section 14.3: Symplectic Geometry**

Whereas Riemannian geometry considers a symmetric inner product, this field studies manifolds with an antisymmetric, non-degenerate 2-form (a symplectic form).

##### **Subsection 14.3.1: Symplectic Manifolds and Hamiltonian Mechanics**

A symplectic manifold is the natural geometric stage (phase space) for the Hamiltonian formulation of classical mechanics. Physical laws such as the conservation of energy are elegantly described as the invariance of the symplectic structure.

### **Chapter 15: Topology**

A field that studies the properties of figures that are preserved under continuous deformation (topological properties). It is also called "rubber-sheet geometry."

#### **Section 15.1: Point-Set Topology**

The basic theory of topology, which studies the general properties of topological spaces.

##### **Subsection 15.1.1: Topological Spaces, Continuous Maps, Homeomorphisms**

We define a topological space by the axioms of open sets. We learn about continuous maps between two topological spaces, and homeomorphisms, whose inverse maps are also continuous. Homeomorphic figures are considered "the same" in topology (for example, a coffee cup and a donut are homeomorphic) [3].

##### **Subsection 15.1.2: Compactness and Connectedness**

Compactness is a generalization of the property of "bounded closed sets" and is an important property for reducing operations involving infinity to finite arguments. Connectedness is a formalization of the intuitive property that a space is "in one piece" [3].

#### **Section 15.2: Algebraic Topology**

A field that classifies spaces by associating algebraic objects (topological invariants) such as groups and rings to topological spaces.

##### **Subsection 15.2.1: The Fundamental Group and Covering Spaces**

The group of homotopy classes of loops (closed curves) in a space is called the fundamental group. It detects "one-dimensional holes" in a space. A covering space is a "larger" space that locally has the same structure as the original space and is closely related to the fundamental group [7].

##### **Subsection 15.2.2: Homology and Cohomology Groups**

Homology groups are algebraic invariants that detect "holes" of various dimensions. For example, the first homology group corresponds to loop-shaped holes, and the second homology group corresponds to cavity-shaped holes. Cohomology groups are a dual concept to homology groups and provide richer information, such as having a product structure [8].

##### **Subsection 15.2.3: Homotopy Groups**

Homotopy groups are a generalization of the fundamental group to higher dimensions. They are defined as the homotopy classes of maps from higher-dimensional spheres and capture more subtle topological properties of a space, but their calculation is generally very difficult [8].

#### **Section 15.3: Differential Topology**

A field that studies differentiable manifolds from the perspective of differentiable maps.

##### **Subsection 15.3.1: Morse Theory**

A theory that reconstructs the topological structure (homology, etc.) of the original manifold by investigating the information of the critical points of a smooth function defined on the manifold.

##### **Subsection 15.3.2: de Rham Cohomology**

A cohomology theory defined using differential forms on a manifold. It surprisingly coincides with combinatorial theories like singular cohomology and shows the deep connection between analytic and topological methods.

### **Chapter 16: Advanced Topics in Geometry**

#### **Section 16.1: Geometric Group Theory**

A relatively new field that considers a group as a geometric object and studies its global properties.

##### **Subsection 16.1.1: Group Actions on Geometric Objects**

We obtain information about the algebraic structure of a group by investigating the orbits and fixed points when the group acts on a space. This perspective has brought geometric intuition to group theory [43].

##### **Subsection 16.1.2: Hyperbolic Groups and CAT(0) Groups**

A hyperbolic group, introduced by Gromov, is a group that abstracts the properties of hyperbolic space, and many finitely presented groups have this property. A CAT(0) space is a generalization of a space with non-positive curvature, and a group that acts on it (a CAT(0) group) is known to have good algorithmic properties. These concepts are connected not only to research in pure mathematics but also to the development of cryptography using group theory [43].

#### **Section 16.2: Complex Geometry**

A field that studies manifolds with complex numbers as coordinates instead of real numbers, i.e., complex manifolds.

##### **Subsection 16.2.1: Kähler Manifolds**

A Kähler manifold is a special complex manifold where a Riemannian structure, a symplectic structure, and a complex structure are well-compatible. A non-singular projective variety that appears in algebraic geometry is a Kähler manifold, and it has a rich theory as an intersection of analysis, geometry, and algebra.

##### **Subsection 16.2.2: Calabi-Yau Manifolds**

A Calabi-Yau manifold, which is a compact Kähler manifold with zero Ricci curvature, has been an important research object in mathematics since its existence was proved by Yau. In particular, it plays a central role in the superstring theory of physics as a model for the extra dimensions of our spacetime [4].

## **Part V: Structures of the Discrete and the Probabilistic**

### **Part Introduction**

In contrast to the analysis and geometry that deal with the continuous world explored in the previous parts, this fifth part focuses on the methodology for mathematically capturing structures consisting of a finite or countable number of objects and phenomena that contain uncertainty or chance. Discrete mathematics deals with objects such as graphs, networks, and combinations, and its theory is an indispensable language for algorithm design and the formulation of optimization problems in computer science [1]. On the other hand, probability theory and statistics rigorously formulate random phenomena based on Kolmogorov's axioms and provide the theoretical foundation for extracting meaningful insights from data [26]. These are extremely practical and important mathematical fields that support scientific discovery, economic forecasting, and the development of artificial intelligence in our data-driven modern society.

### **Chapter 17: Discrete Mathematics**

#### **Section 17.1: Combinatorics**

A field that studies the arrangement and selection of elements of a finite set, i.e., the art of "counting."

##### **Subsection 17.1.1: Basic Counting Principles**

We start with basic principles such as the sum rule and the product rule, and learn the calculation of permutations and combinations. The binomial theorem gives a polynomial expansion whose coefficients are the number of combinations.

##### **Subsection 17.1.2: Generating Functions**

We learn a powerful technique that transforms a combinatorial problem into a problem of algebraic manipulation of functions by considering a formal power series whose coefficients are the sequence we want to count (a generating function).

##### **Subsection 17.1.3: Ramsey Theory**

A field that deals with the idea that "in any sufficiently large structure, there is always some kind of ordered substructure." For example, Ramsey's theorem shows that in a sufficiently large party, there is always a group of three people who are mutual acquaintances or a group of three people who are mutual strangers. This is one of the profound areas of combinatorics [46].

#### **Section 17.2: Graph Theory**

A field that studies figures consisting of points (vertices) and lines connecting them (edges), i.e., graphs. A graph is a universal language for modeling various real-world relationships such as social networks, transportation networks, and molecular structures [47].

##### **Subsection 17.2.1: Basic Concepts: Paths, Cycles, Connectivity**

We define the basic vocabulary of graph theory, such as vertices, edges, degrees, paths, cycles, and connectivity. We learn about various types of graphs, such as directed and undirected graphs, and weighted graphs [47].

##### **Subsection 17.2.2: Trees and Spanning Trees**

A connected graph with no cycles is called a tree. A tree is suitable for modeling hierarchical structures and branching processes. The problem of finding a spanning tree, which is a tree that connects all the vertices of a given graph, especially a minimum spanning tree, whose sum of edge weights is minimum, is important in network design.

##### **Subsection 17.2.3: Eulerian and Hamiltonian Paths**

The condition for the existence of an Eulerian path (a path that traverses every edge exactly once), which originated from the problem of the seven bridges of Königsberg, is completely characterized by the degrees of the vertices. On the other hand, the problem of determining the existence of a Hamiltonian path, which visits every vertex exactly once, is known to be generally very difficult (NP-hard) [46].

##### **Subsection 17.2.4: Network Flows**

A field that deals with the problem of how much "flow" (goods, information, etc.) can be sent from a source to a sink in a network where the edges have capacities. The max-flow min-cut theorem reveals the beautiful duality of this problem [46].

##### **Subsection 17.2.5: Application: Network Science and Algorithms**

Graph theory is not limited to the study of static structures. From a modern perspective, the study of algorithms for efficiently solving problems on graphs is extremely important. For example, the solution of the shortest path problem, such as Dijkstra's algorithm used in car navigation route search, and the solution of the maximum flow problem, such as the Ford-Fulkerson algorithm used in the design of communication networks, are representative of the algorithmic aspects of graph theory [46]. Furthermore, its applications to physical and engineering systems, such as the modeling of electrical circuit networks and porous materials, are also wide-ranging [49].

### **Chapter 18: Probability Theory**

#### **Section 18.1: Foundations of Probability**

We construct a framework for rigorously handling random phenomena mathematically.

##### **Subsection 18.1.1: Probability Spaces and Kolmogorov's Axioms**

We reconstruct probability theory in the language of measure theory. We define a probability space, which consists of a sample space (the set of all possible outcomes), an event (a subset of the sample space), and a probability measure (the assignment of a probability to each event), and learn the axioms that probability must satisfy (Kolmogorov's axioms).

##### **Subsection 18.1.2: Conditional Probability and Bayes' Theorem**

We define conditional probability, which is the probability of an event occurring given that another event has occurred. Bayes' theorem is a fundamental formula for updating a prior probability from new data to a posterior probability and plays a central role in Bayesian statistics and machine learning [50].

##### **Subsection 18.1.3: Random Variables and Probability Distributions**

A function that associates a numerical value to the outcome of a random experiment is called a random variable. A probability distribution describes the probability of a random variable taking on a specific value.

#### **Section 18.2: Probability Distributions and Expectation**

##### **Subsection 18.2.1: Key Discrete and Continuous Distributions**

We learn the properties of discrete probability distributions such as the Bernoulli, binomial, and Poisson distributions, and continuous probability distributions such as the uniform, normal, and exponential distributions, and what kinds of phenomena they are suitable for modeling.

##### **Subsection 18.2.2: Expectation, Variance, and Moments**

The expected value represents the "average value" of a random variable, and the variance is an indicator of how much its values are "scattered" around the expected value. Moments, which generalize these, are used to characterize the shape of a probability distribution.

#### **Section 18.3: Limit Theorems**

We learn the surprising universal laws that the sum of a large number of independent random variables exhibits.

##### **Subsection 18.3.1: The Law of Large Numbers (Weak and Strong)**

When a large number of independent trials are repeated, the sample mean approaches the true mean (expected value). The law of large numbers is a mathematical rigorization of this intuitive fact. The weak law asserts convergence in probability, while the stronger strong law asserts almost sure convergence [51].

##### **Subsection 18.3.2: The Central Limit Theorem**

Whatever the original distribution, the distribution of the sum (or mean) of a large number of independent and identically distributed random variables can be approximated by a normal distribution as the sample size increases. This central limit theorem is one of the most important results in probability theory, explaining why the normal distribution appears universally in statistics [51].

#### **Section 18.4: Stochastic Processes**

We model phenomena that fluctuate randomly over time.

##### **Subsection 18.4.1: Markov Chains**

A stochastic process with the property that the future state depends only on the present state and not on the past states (the Markov property). It is used to model things like weather changes and random surfing on web pages.

##### **Subsection 18.4.2: Poisson Processes**

A process that models the occurrence of random events at a constant rate. Examples include the arrival of phone calls and the decay of radioactive material.

##### **Subsection 18.4.3: Brownian Motion Revisited**

The most basic example of a stochastic process whose state fluctuates in continuous time. It plays a central role in physics and financial engineering as a model for stock price fluctuations and the random motion of fine particles.

### **Chapter 19: Mathematical Statistics**

The mathematical theory for extracting useful information from data and making decisions under uncertainty.

#### **Section 19.1: Descriptive and Inferential Statistics**

##### **Subsection 19.1.1: Sampling Distributions**

The probability distribution of a statistic (sample mean, sample variance, etc.) calculated from a sample randomly drawn from a population is called a sampling distribution. By the central limit theorem, the distribution of the sample mean is often approximated by a normal distribution.

#### **Section 19.2: Estimation Theory**

We infer unknown population parameters from sample data.

##### **Subsection 19.2.1: Point Estimation: Maximum Likelihood, Method of Moments**

We learn methods of point estimation, which estimate a parameter with a single value. The maximum likelihood method, which estimates the parameter so as to maximize the probability (likelihood) of obtaining the observed data, is the most widely used method.

##### **Subsection 19.2.2: Interval Estimation**

We estimate an interval with a certain probability (confidence level) that the parameter is contained within it. A confidence interval provides a way to quantitatively evaluate the uncertainty of an estimate.

#### **Section 19.3: Hypothesis Testing**

We probabilistically judge whether a hypothesis about a population is correct or not based on sample data.

##### **Subsection 19.3.1: Framework of Testing (Type I & II Errors)**

We set up a null hypothesis and an alternative hypothesis, calculate a test statistic, and judge whether to reject the null hypothesis or not. We understand the trade-off between a Type I error, which is incorrectly rejecting a true null hypothesis, and a Type II error, which is not rejecting a false null hypothesis.

##### **Subsection 19.3.2: Common Tests: t-test, Chi-squared, F-test**

We learn about important tests for applications, such as the t-test, which is used to test the difference between means; the chi-squared test, which is used to test variance and goodness of fit; and the F-test, which is used in the analysis of variance (ANOVA) to compare the means of multiple groups.

#### **Section 19.4: Modern Statistical Methods**

##### **Subsection 19.4.1: Bayesian Statistics**

A field that considers the parameter itself as a random variable and calculates its posterior distribution from the data using Bayes' theorem. It can incorporate subjective prior knowledge into the model and has been widely used in recent years with the improvement of computational power.

##### **Subsection 19.4.2: Multivariate Analysis**

A group of statistical methods for handling multiple variables simultaneously. They include principal component analysis, factor analysis, and cluster analysis, and are used to visualize and summarize the structure of high-dimensional data [56].

##### **Subsection 19.4.3: Design of Experiments**

A statistical method for optimizing the planning of experiments and surveys to obtain efficient and reliable conclusions. It includes factorial designs and randomized block designs [56].

## **Part VI: Frontiers of Mathematical Sciences**

### **Part Introduction**

Mathematics develops as a pure science that pursues its own internal logic and beauty, while also functioning as a powerful language and tool for understanding, predicting, and controlling the complex phenomena of the real world, such as science and technology, the economy, and society. Although the distinction between pure and applied mathematics existed historically, in modern times its boundary has become increasingly blurred, and both are developing while stimulating each other [4]. In this final part, we explore how the theories of algebra, analysis, and geometry cultivated in the previous parts are applied to the most dynamic challenges of modern society. From computational mathematics, which performs large-scale numerical simulations made possible for the first time by the development of computers, to mathematical physics, which describes the fundamental laws of physics in the language of mathematics, to information theory and cryptography, which are the foundations of the digital society, and to the most active fields of modern times such as artificial intelligence (AI), data science, and financial engineering, we will survey the frontiers of knowledge that mathematics is opening up [56].

The following table visually shows the bridge between the main concepts of pure mathematics explored in this textbook and the applied fields detailed in this Part VI. This table aims to clarify the correspondence of how the learning of abstract theory leads to concrete problem-solving ability. For example, it can be seen at a glance that the theory of finite fields learned in Chapter 5 is indispensable for understanding the error-correcting codes and cryptography of Chapter 22, or that the differential geometry of Chapter 14 is the mathematical language itself of the general theory of relativity of Chapter 21. Being aware of this correspondence is essential for understanding mathematics not as a collection of fragmented knowledge, but as one grand intellectual system.

| Pure Mathematical Concept | Key Application Area | Relevant Chapters |
| :--- | :--- | :--- |
| Linear Algebra (Eigenvalues, SVD) | Data Science (PCA), Machine Learning | 4, 24 |
| Ring/Field Theory (Finite Fields) | Information Theory (ECC), Cryptography | 5, 22 |
| Number Theory (Prime Factorization) | Cryptography (RSA) | 6, 22 |
| Differential Equations (PDEs) | Physics (Fluid Dynamics), Engineering | 12, 21 |
| Stochastic Diff. Equations (SDEs) | Mathematical Finance (Option Pricing) | 12, 25 |
| Differential Geometry (Curvature) | Physics (General Relativity) | 14, 21 |
| Topology (Homology) | Data Science (Topological Data Analysis) | 15, 24 |
| Graph Theory (Networks) | Comp. Sci., Social Sci., Operations Research | 17, 23 |
| Probability/Statistics | Data Sci., Machine Learning, Fin. Eng. | 18, 19, 24, 25 |
| Optimization Theory | Machine Learning, Economics, Op. Research | 23, 24, 25 |

### **Chapter 20: Computational Mathematics and Numerical Analysis**

A field that studies algorithms for obtaining approximate solutions using computers for mathematical problems that are difficult to solve analytically.

#### **Section 20.1: Fundamentals of Numerical Analysis**

##### **Subsection 20.1.1: Error Analysis (Round-off, Truncation)**

We analyze the errors that inevitably accompany numerical calculations. Round-off error is due to the finite-digit representation of computers, and truncation error is due to approximating an infinite process (series or integral) with a finite one. Evaluating the propagation and accumulation of these errors is essential for guaranteeing the reliability of a numerical solution.

##### **Subsection 20.1.2: Root-finding Algorithms for Nonlinear Equations**

We learn iterative methods for finding x such that f(x)=0. The bisection method, Newton's method, and the secant method are representative algorithms.

#### **Section 20.2: Numerical Linear Algebra**

A field that studies algorithms for solving linear algebra problems efficiently and stably on a computer.

##### **Subsection 20.2.1: Direct and Iterative Methods for Linear Systems**

We learn methods for solving large systems of linear equations Ax=b. Direct methods (Gaussian elimination, LU decomposition, etc.) give an exact solution in a finite number of calculations but may be unsuitable for large-scale problems. Iterative methods (Jacobi method, Gauss-Seidel method, conjugate gradient method, etc.) are methods that successively improve an approximate solution.

##### **Subsection 20.2.2: Numerical Methods for Eigenvalue Problems**

We learn algorithms for numerically calculating the eigenvalues and eigenvectors of a matrix. The power method and the QR algorithm are representative. The eigenvalue problem for large matrices appears in many situations in scientific and technological calculations, such as quantum chemistry calculations and structural analysis [60].

#### **Section 20.3: Numerical Solution of Differential Equations**

##### **Subsection 20.3.1: Methods for ODEs, e.g., Runge-Kutta**

We successively approximate the solution of an initial value problem by dividing time into discrete steps. We compare the accuracy and stability of various algorithms, from the Euler method to the more accurate Runge-Kutta methods [60].

##### **Subsection 20.3.2: Methods for PDEs: Finite Difference, Finite Element**

We learn the basics of numerical solution methods for partial differential equations, such as the finite difference method, which discretizes space and time into a grid and approximates partial derivatives with differences, and the finite element method, which approximates the solution space with a finite number of basis functions and solves the equation based on a variational principle. These are the core technologies of engineering applications such as fluid simulations and structural analysis [60].

#### **Section 20.4: Verified Numerical Computation**

A method for deriving mathematically correct conclusions by giving a rigorous error bound, including round-off error, to the results of numerical calculations by a computer. Interval arithmetic is its basis [59].

### **Chapter 21: Mathematical Physics**

A field that describes the theories of physics in the language of rigorous mathematics and studies their structure.

#### **Section 21.1: Classical and Analytical Mechanics**

##### **Subsection 21.1.1: Lagrangian and Hamiltonian Formalisms**

We reformulate Newton's equations of motion in a more sophisticated form based on the principle of least action. The Lagrangian formalism considers the difference between the kinetic and potential energy of a system (the Lagrangian), while the Hamiltonian formalism considers the total energy of the system (the Hamiltonian). These provide a natural bridge to quantum mechanics and statistical mechanics [3].

#### **Section 21.2: Electromagnetism and Maxwell's Equations**

We elegantly express Maxwell's equations, which describe the behavior of electric and magnetic fields, using the language of vector analysis and differential forms. The theoretical prediction of the existence of electromagnetic waves from these equations is a great success story of mathematical physics [3].

#### **Section 21.3: Theory of Relativity**

##### **Subsection 21.3.1: Special Relativity and Minkowski Space**

From the principle of the constancy of the speed of light and the principle of relativity, we derive that time and space are relative to the observer. Physical spacetime is described as a 4-dimensional Minkowski space with a different sign in the inner product.

##### **Subsection 21.3.2: General Relativity and Differential Geometry**

Einstein's theory, which regards gravity as the "curvature of spacetime." Its mathematical language is differential geometry itself, which we learned in Part IV. Spacetime is modeled as a Riemannian manifold (more precisely, a Lorentzian manifold), and its metric tensor (which determines the local geometry of spacetime) has a curvature determined by the distribution of matter and energy. The equation that describes this relationship is the Einstein field equations. The free fall of an object is explained as motion along a geodesic of this curved spacetime [61].

#### **Section 21.4: Mathematical Foundations of Quantum Mechanics**

##### **Subsection 21.4.1: Hilbert Spaces and Operators**

The state of a quantum system is represented by a vector in a Hilbert space (a state vector), and an observable physical quantity (position, momentum, energy, etc.) is represented by a self-adjoint operator on the Hilbert space. The observed value is obtained as an eigenvalue of that operator.

##### **Subsection 21.4.2: The Schrödinger Equation**

The fundamental partial differential equation that describes the time evolution of a state vector. Its solution probabilistically predicts the future state of the system [3].

#### **Section 21.5: Mathematics of Modern Physics**

##### **Subsection 21.5.1: Quantum Field Theory and Gauge Theory**

A theory that integrates quantum mechanics and special relativity and describes the creation and annihilation of elementary particles. Gauge theory is a framework that derives the interaction between particles from the local symmetry of physical laws (gauge symmetry), and the theory of fiber bundles and connections in differential geometry is its mathematical foundation [4].

##### **Subsection 21.5.2: String Theory and Higher-Dimensional Geometry**

A theory that considers elementary particles not as points but as vibrating "strings." It is considered a promising candidate for a theory of quantum gravity, and its consistent formulation is deeply connected to higher-dimensional algebraic geometry and complex geometry, such as Calabi-Yau manifolds [4].

##### **Subsection 21.5.3: Fluid Dynamics and the Navier-Stokes Equations**

The Navier-Stokes equations are nonlinear partial differential equations that describe the motion of fluids such as water and air. Their applications are extremely wide, from weather forecasting to aircraft design, but their mathematical properties (especially whether a smooth solution always exists) are still not understood and are one of the greatest challenges in modern mathematics [67].

### **Chapter 22: Mathematics of Information and Computation**

#### **Section 22.1: Theory of Computation**

A field that mathematically explores what computation is, its capabilities, and its limits.

##### **Subsection 22.1.1: Automata and Language Theory**

We learn about simple computational models like finite automata and the class of languages they can recognize (regular languages). This has practical applications in the lexical analysis of compilers, among other things.

##### **Subsection 22.1.2: Computability: Turing Machines and Undecidability**

We define a Turing machine, which models the principle of all computers, and rigorously formalize the concept of "algorithmically computable." We show that there are "undecidable problems," such as Turing's halting problem, that cannot be solved by any algorithm.

##### **Subsection 22.1.3: Complexity Theory: P, NP, and the P vs NP Problem**

A field that classifies the "difficulty" of a problem by the amount of computation time or memory required to solve it. P is the class of "easy" problems that can be solved in polynomial time, and NP is the class of problems whose solutions can be verified in polynomial time. Whether P and NP are equal (the P vs NP problem) is the most important unsolved problem in computer science, and if P=NP were shown, many optimization problems that are currently considered difficult could be solved efficiently, which would have an immeasurable impact on society [70].

#### **Section 22.2: Information Theory**

A theory founded by Shannon concerning the quantification of information and the limits of communication.

##### **Subsection 22.2.1: Entropy and Mutual Information**

We define entropy as an indicator that quantifies the uncertainty or amount of information of an information source. Mutual information measures the amount of information shared between two random variables.

##### **Subsection 22.2.2: Channel Coding Theorem**

The fundamental theorem of information theory, which shows that even in a noisy communication channel, as long as the rate does not exceed its capacity (the channel capacity), there exists a coding scheme that can make the error rate arbitrarily small.

#### **Section 22.3: Cryptography**

Mathematical techniques for ensuring the confidentiality, integrity, and authentication of information.

##### **Subsection 22.3.1: Symmetric and Public-Key Cryptography**

We learn the principles of symmetric-key cryptography, which uses the same key for encryption and decryption, and public-key cryptography, which uses different keys. Public-key cryptography solved the key distribution problem and enabled secure communication on the Internet (SSL/TLS, etc.).

##### **Subsection 22.3.2: RSA and the Integer Factorization Problem**

We learn the mechanism of RSA encryption, a representative public-key cryptosystem. Its security is based on the difficulty of a number-theoretic problem, namely that the prime factorization of a large composite number is very difficult for a computer.

##### **Subsection 22.3.3: Elliptic Curve Cryptography and the Discrete Logarithm Problem**

A cryptosystem that uses the difficulty of the discrete logarithm problem in the group of points on an elliptic curve, an object of algebraic geometry. Since it can achieve equivalent security with a shorter key length than RSA encryption, it is widely used in resource-constrained environments such as IC cards.

##### **Subsection 22.3.4: Applications of Geometric Group Theory**

Research is underway to construct new cryptosystems using non-commutative groups, especially groups with complex structures studied in geometric group theory. This is also connected to the development of next-generation cryptographic technology (post-quantum cryptography) in preparation for the possibility that existing cryptosystems will be broken by quantum computers [44].

#### **Section 22.4: Coding Theory**

##### **Subsection 22.4.1: Basics of Error-Detecting and -Correcting Codes**

A technology that adds redundancy to the original information to automatically detect and correct errors that occur during data communication or recording. The Hamming code is a basic example.

##### **Subsection 22.4.2: Reed-Solomon Codes and Finite Fields**

Reed-Solomon codes, which have excellent correction capability for burst errors (consecutive errors), are constructed using polynomials over finite fields (Galois fields), which we learned about in Chapter 5. Encoding corresponds to the operation of treating the information data as a polynomial and calculating the remainder when divided by a specific generator polynomial. This code is used to ensure the reliability of information in many digital technologies around us, such as QR codes, CDs, and digital broadcasting [6].

### **Chapter 23: Optimization and Operations Research**

A group of mathematical methods for finding a solution that maximizes or minimizes a certain objective function under given constraints.

#### **Section 23.1: Foundations of Mathematical Optimization**

##### **Subsection 23.1.1: Linear Programming and the Simplex Method**

The most basic optimization problem where the objective function and constraints are all linear. It is applied to resource allocation problems and transportation problems, among others. The simplex method is known as its efficient solution method.

##### **Subsection 23.1.2: Nonlinear Programming and Gradient-Based Methods**

A more general optimization problem that includes nonlinear terms in the objective function or constraints. Gradient descent is an iterative method that searches for a local minimum by gradually moving in the direction where the function value decreases most steeply (the opposite direction of the gradient), and it plays a central role in the learning of models in machine learning in particular [75].

#### **Section 23.2: Convex Optimization**

A special class of optimization problems where the objective function is a convex function and the feasible region is a convex set.

##### **Subsection 23.2.1: Convex Sets and Functions**

A set such that the line segment connecting any two points is again contained within it is called a convex set, and a function whose graph bulges downward is called a convex function.

##### **Subsection 23.2.2: Lagrangian Duality**

For the original optimization problem (the primal problem), another optimization problem called the dual problem is constructed using the Lagrangian function. In convex optimization, the optimal values of the primal and dual problems often coincide (strong duality), which leads to the development of efficient algorithms.

#### **Section 23.3: Combinatorial Optimization**

A problem of finding the optimal combination from a discrete set of objects.

##### **Subsection 23.3.1: The Traveling Salesperson Problem and Integer Programming**

The traveling salesperson problem, which is the problem of finding the shortest route that visits all cities exactly once and returns to the starting point, is a representative difficult problem in combinatorial optimization. Integer programming, where the variables can only take on integer values, is a general framework for formulating such problems.

##### **Subsection 23.3.2: Discrete Convex Analysis**

A new field that constructs an analogy of the theory of continuous convex analysis for functions with discrete variables. It provides a unified perspective and efficient solution methods for discrete optimization problems with a certain "good" structure [76].

#### **Section 23.4: Game Theory**

A field that mathematically analyzes strategic situations where multiple decision-making agents (players) mutually influence each other.

##### **Subsection 23.4.1: Strategic-Form Games and Nash Equilibrium**

A game where each player chooses a strategy simultaneously is represented in strategic form. A Nash equilibrium is a stable combination of strategies where no player has an incentive to change their strategy alone.

##### **Subsection 23.4.2: Extensive-Form Games and Subgame Perfect Equilibrium**

A game where players choose actions sequentially is represented in extensive form. A subgame perfect equilibrium is a more refined equilibrium concept that requires that a rational choice be made at every stage of the game.

### **Chapter 24: Mathematics of Data Science and Machine Learning**

A field that explores the mathematical principles behind machine learning algorithms that learn patterns from data and make predictions on unknown data.

#### **Section 24.1: Mathematical Foundations of Machine Learning**

Machine learning is built on a deep fusion of classical mathematical fields such as linear algebra, analysis, and probability/statistics.

##### **Subsection 24.1.1: Linear Algebra: SVD and PCA**

Dimensionality reduction, which projects high-dimensional data into a low-dimensional space while preserving its essential information, is an important preprocessing step in data analysis. Principal component analysis (PCA) is a method that finds the directions in which the variance of the data is maximized, and its calculation is reduced to the eigenvalue decomposition of the covariance matrix of the data matrix, or the singular value decomposition (SVD) of the data matrix itself [77].

##### **Subsection 24.1.2: Vector Calculus: Gradient Descent and Optimization**

The learning process of a machine learning model is essentially an optimization problem. The goal is to define the error between the model's prediction and the true value (the loss function) and find the model's parameters that minimize that loss function. Gradient descent is the most basic optimization algorithm that minimizes the loss by calculating the gradient of the loss function with respect to the parameters (the derivative of a multivariable function) and repeatedly updating the parameters in the opposite direction [77]. This process shows the deep connection between machine learning and optimization theory [80].

##### **Subsection 24.1.3: Probability/Statistics: Bayesian Inference and Probabilistic Models**

Probability theory and statistics are indispensable for modeling the uncertainty inherent in data. Many machine learning models are based on a probabilistic model that assumes that the data is generated from a specific probability distribution. Bayesian inference provides a framework for updating the probability distribution of a model's parameters using observed data and allows for the quantitative evaluation of the model's uncertainty [50].

#### **Section 24.2: Supervised Learning**

A field that learns the relationship between input and output from pairs of input data and their corresponding correct labels (training data).

##### **Subsection 24.2.1: Linear Regression and Regularization**

The simplest model that predicts an output variable as a linear combination of input variables. To prevent the model from becoming too complex and overfitting to the training data, a technique called regularization, which penalizes the size of the parameters, is used. From a Bayesian perspective, this corresponds to assuming a prior distribution for the parameters [83].

##### **Subsection 24.2.2: Logistic Regression and Support Vector Machines (SVM)**

Logistic regression solves a binary classification problem by interpreting the output as a probability. A support vector machine (SVM) aims for high generalization performance by finding the boundary (hyperplane) that separates the data of different classes with the maximum margin. This problem is formulated as a convex quadratic programming problem, an optimization problem [84].

##### **Subsection 24.2.3: Neural Networks and Deep Learning**

A neural network, which is a layered combination of a large number of simple computational units (neurons), can approximate very complex nonlinear functions. Deep learning, which has deep layers, has achieved revolutionary results in the fields of image recognition and natural language processing. Its learning is performed by an algorithm called backpropagation, which is an efficient way to execute gradient descent.

#### **Section 24.3: Unsupervised Learning**

A field that discovers the underlying structure or patterns from data without correct labels.

##### **Subsection 24.3.1: Clustering: k-means, Hierarchical**

A field that divides data into several groups (clusters) based on similarity. k-means is a method that optimizes a specified number of cluster centers, and hierarchical clustering discovers the hierarchical group structure of the data.

##### **Subsection 24.3.2: Dimensionality Reduction: PCA, t-SNE**

A field that reduces the dimension of data for the visualization of high-dimensional data or for subsequent analysis. Whereas PCA captures linear structures, methods like t-SNE are superior for visualizing nonlinear structures by embedding them in a low-dimensional space while preserving the neighborhood relationships in the high-dimensional space.

#### **Section 24.4: Frontiers in Data Analysis**

##### **Subsection 24.4.1: Topological Data Analysis (TDA) and Persistent Homology**

A new approach that analyzes the "shape" of data using the tools of topology learned in Part IV, especially homology. Persistent homology, which tracks when topological features (connected components, loops, voids, etc.) are created and destroyed while changing the scale for point cloud data, is its central method. This allows for the extraction of higher-order structural features of data that cannot be captured by conventional statistical methods. It is expected to be applied in a wide range of fields, such as materials science, life sciences, and image analysis [42].

##### **Subsection 24.4.2: Graph Neural Networks**

A deep learning model for directly handling data with a graph structure, such as social networks and molecular structures. It learns the structural features of the entire graph by repeating a process where each vertex aggregates the information of its neighboring vertices to update its own representation [46].

### **Chapter 25: Mathematical Finance and Mathematical Economics**

#### **Section 25.1: Mathematical Finance**

A field that mathematically models the behavior of financial markets and performs the pricing and risk management of financial derivatives.

##### **Subsection 25.1.1: Arbitrage Theory and Risk-Neutral Probability**

The basic assumption in financial markets is that "there are no opportunities to make a profit without risk (arbitrage)." From this no-arbitrage assumption, it is derived that there exists a special probability measure (a risk-neutral probability measure) that consistently explains market prices.

##### **Subsection 25.1.2: The Black-Scholes Equation and Option Pricing**

By modeling the fluctuation of stock prices with a stochastic differential equation (geometric Brownian motion) and using the no-arbitrage principle and Itō's formula, the partial differential equation that the price of a European option must satisfy (the Black-Scholes equation) is derived. The Black-Scholes formula, obtained by solving this equation, gives the theoretical price of an option with five parameters: the underlying asset price, the strike price, the maturity, the interest rate, and the volatility. This theory became the starting point of modern financial engineering [40].

##### **Subsection 25.1.3: Portfolio Theory**

A field that considers how to allocate investments among multiple assets to minimize risk while maximizing expected return. It is important to consider the correlation between assets.

#### **Section 25.2: Mathematical Economics**

A field that rigorously formulates and analyzes economic theory in the language of mathematics.

##### **Subsection 25.2.1: General Equilibrium Theory**

A field that proves the existence of a price system where demand and supply are simultaneously in equilibrium in all markets in an economy with a large number of consumers and producers (the existence of a general equilibrium), using mathematical tools such as the fixed-point theorem.

##### **Subsection 25.2.2: Mathematical Foundations of Econometrics**

We learn the mathematical theory behind econometrics, which statistically analyzes economic data and performs the verification of economic theory and economic forecasting. Regression analysis and time series analysis are its central components [60].

#### **References**

[1] Portal:Mathematics/Fields - Wikipedia, accessed July 5, 2025, [https://en.wikipedia.org/wiki/Portal:Mathematics/Fields](https://en.wikipedia.org/wiki/Portal:Mathematics/Fields)
[2] Mathematics - Wikipedia, accessed July 5, 2025, [https://en.wikipedia.org/wiki/Mathematics](https://en.wikipedia.org/wiki/Mathematics)
[3] Scope of University Mathematics - Nagomi, a Math School for Adults, accessed July 5, 2025, [http://imakarasuugaku.com/math/collegemath.html](http://imakarasuugaku.com/math/collegemath.html) (in Japanese)
[4] Introduction to the Department of Mathematics, Faculty of Science, The University of Tokyo, accessed July 5, 2025, [https://www.s.u-tokyo.ac.jp/ja/admission/undergraduate/pdf/ms2022.pdf](https://www.s.u-tokyo.ac.jp/ja/admission/undergraduate/pdf/ms2022.pdf) (in Japanese)
[5] First Day of Learning Category Theory | Kenichi Aoki - note, accessed July 5, 2025, [https://note.com/aokikenichi/n/nd761801ce740](https://note.com/aokikenichi/n/nd761801ce740) (in Japanese)
[6] A Study on Error-Correcting Codes over Integer Residue Rings and their Application to Digital Communication Systems - The University of Tokyo Repository, accessed July 5, 2025, [https://repository.dl.itc.u-tokyo.ac.jp/record/2743/files/K-214739.pdf](https://repository.dl.itc.u-tokyo.ac.jp/record/2743/files/K-214739.pdf) (in Japanese)
[7] List of Specialized Subjects, Kobe University, accessed July 5, 2025, [http://www.math.kobe-u.ac.jp/home-j/ichiran.html](http://www.math.kobe-u.ac.jp/home-j/ichiran.html) (in Japanese)
[8] Curriculum of the Department of Mathematics - Graduate School of Mathematical Sciences, The University of Tokyo, accessed July 5, 2025, [https://www.ms.u-tokyo.ac.jp/kyoumu/math_curriculum.html](https://www.ms.u-tokyo.ac.jp/kyoumu/math_curriculum.html) (in Japanese)
[9] The Fundamental Theorem of Algebra - Notes by Naughie, accessed July 5, 2025, [https://notes.naughie.com/galois-theory/fundamental-thm-of-algebra.pdf](https://notes.naughie.com/galois-theory/fundamental-thm-of-algebra.pdf)
[10] Group Theory is Fun! Part 1. A Summary of the Basics of Abstract Algebra, which also forms the basis of Cryptography | by Daisuke Ishii | 【Team AI】Machine Learning Community in Tokyo | Medium, accessed July 5, 2025, [https://medium.com/ai-business/group-theory-1-a2be8a7a87d0](https://medium.com/ai-business/group-theory-1-a2be8a7a87d0)
[11] 1 Introduction 2 Reed-Solomon Codes 3 QR Code Standard and Structure (JIS-X-0510) 4 Experiment, accessed July 5, 2025, [https://kaji.w.waseda.jp/MasterThesis/2023dateR.pdf](https://kaji.w.waseda.jp/MasterThesis/2023dateR.pdf) (in Japanese)
[12] Introduction to Reed-Solomon Codes: Encoding and Error Detection - Qiita, accessed July 5, 2025, [https://qiita.com/kerupani129/items/b68342cd3aa3d9841492](https://qiita.com/kerupani129/items/b68342cd3aa3d9841492) (in Japanese)
[13] Technical Explanation: Error Correction Processing Speed by 8-bit Microcomputer, accessed July 5, 2025, [http://www.rf-world.jp/bn/RFW07/p115-116.htm](http://www.rf-world.jp/bn/RFW07/p115-116.htm) (in Japanese)
[14] Syllabus | Theory of Numbers | Mathematics - MIT OpenCourseWare, accessed July 5, 2025, [https://ocw.mit.edu/courses/18-781-theory-of-numbers-spring-2012/pages/syllabus/](https://ocw.mit.edu/courses/18-781-theory-of-numbers-spring-2012/pages/syllabus/)
[15] Number Theory in Mathematics - GeeksforGeeks, accessed July 5, 2025, [https://www.geeksforgeeks.org/engineering-mathematics/number-theory/](https://www.geeksforgeeks.org/engineering-mathematics/number-theory/)
[16] Algebraic number theory - Wikipedia, accessed July 5, 2025, [https://en.wikipedia.org/wiki/Algebraic_number_theory](https://en.wikipedia.org/wiki/Algebraic_number_theory)
[17] Algebraic Number Theory - James Milne, accessed July 5, 2025, [https://www.jmilne.org/math/CourseNotes/ANT.pdf](https://www.jmilne.org/math/CourseNotes/ANT.pdf)
[18] Math 7315: Algebraic Number Theory - Homepage - Evan Dummit, accessed July 5, 2025, [https://dummit.cos.northeastern.edu/teaching_fa24_7315](https://dummit.cos.northeastern.edu/teaching_fa24_7315)
[19] List of algebraic number theory topics - Wikipedia, accessed July 5, 2025, [https://en.wikipedia.org/wiki/List_of_algebraic_number_theory_topics](https://en.wikipedia.org/wiki/List_of_algebraic_number_theory_topics)
[20] Analytic Number Theory - Kotobank, accessed July 5, 2025, [https://kotobank.jp/word/%E8%A7%A3%E6%9E%90%E7%9A%84%E6%95%B4%E6%95%B0%E8%AB%96-42587](https://kotobank.jp/word/%E8%A7%A3%E6%9E%90%E7%9A%84%E6%95%B4%E6%95%B0%E8%AB%96-42587) (in Japanese)
[21] Analytic number theory - Wikipedia, accessed July 5, 2025, [https://en.wikipedia.org/wiki/Analytic_number_theory](https://en.wikipedia.org/wiki/Analytic_number_theory)
[22] Analytic Number Theory - Wikipedia (Japanese), accessed July 5, 2025, [https://ja.wikipedia.org/wiki/%E8%A7%A3%E6%9E%90%E7%9A%84%E6%95%B4%E6%95%B0%E8%AB%96](https://ja.wikipedia.org/wiki/%E8%A7%A3%E6%9E%90%E7%9A%84%E6%95%B4%E6%95%B0%E8%AB%96)
[23] Analytic Number Theory – Notes and Study Guides | Fiveable, accessed July 5, 2025, [https://library.fiveable.me/analytic-number-theory](https://library.fiveable.me/analytic-number-theory)
[24] en.wikipedia.org, accessed July 5, 2025, [https://en.wikipedia.org/wiki/Analytic_number_theory#:~:text=Branches%20of%20analytic%20number%20theory,-Analytic%20number%20theory&text=Multiplicative%20number%20theory%20deals%20with,on%20primes%20in%20arithmetic%20progressions.](https://en.wikipedia.org/wiki/Analytic_number_theory#:~:text=Branches%20of%20analytic%20number%20theory,-Analytic%20number%20theory&text=Multiplicative%20number%20theory%20deals%20with,on%20primes%20in%20arithmetic%20progressions.)
[25] What is Analytic Number Theory? - Weblio Dictionary, accessed July 5, 2025, [https://www.weblio.jp/content/%E8%A7%A3%E6%9E%90%E7%9A%84%E6%95%B4%E6%95%B0%E8%AB%96](https://www.weblio.jp/content/%E8%A7%A3%E6%9E%90%E7%9A%84%E6%95%B4%E6%95%B0%E8%AB%96) (in Japanese)
[26] Mathematics - Wikipedia, accessed July 5, 2025, [https://en.wikipedia.org/wiki/Mathematics](https://en.wikipedia.org/wiki/Mathematics)
[27] Introduction to Algebraic Geometry, New Edition / Kenji Ueno | Natural Science Books - Iwanami Shoten, accessed July 5, 2025, [https://www.iwanami.co.jp/book/b657214.html](https://www.iwanami.co.jp/book/b657214.html) (in Japanese)
[28] Tokyo Institute of Technology - Department of Mathematics, accessed July 5, 2025, [https://www.math.titech.ac.jp/files/main22.pdf](https://www.math.titech.ac.jp/files/main22.pdf) (in Japanese)
[29] Linear Algebra I, Compulsory Subject for Teacher's License Acquisition, Number of Credits, accessed July 5, 2025, [https://www.mext.go.jp/content/20240214_mxt_kyoikujinzai01-000033885_4.pdf](https://www.mext.go.jp/content/20240214_mxt_kyoikujinzai01-000033885_4.pdf) (in Japanese)
[30] Product Details (Reference) | Knowledge Worker, accessed July 5, 2025, [https://kw.maruzen.co.jp/ims/itemDetailReference.html;jsessionid=B5A5C0DA18503EFA15DBE7B26695F443?itmCd=1033194227&mbis_token_html_key=4d38cde59b50b8045235a3325a8a46f2](https://kw.maruzen.co.jp/ims/itemDetailReference.html;jsessionid=B5A5C0DA18503EFA15DBE7B26695F443?itmCd=1033194227&mbis_token_html_key=4d38cde59b50b8045235a3325a8a46f2) (in Japanese)
[31] Basics of Complex Functions - Hitotsubashi University, accessed July 5, 2025, [https://www1.econ.hit-u.ac.jp/kawahira/courses/kansuron.pdf](https://www1.econ.hit-u.ac.jp/kawahira/courses/kansuron.pdf) (in Japanese)
[32] Kyoritsu Lecture Series: Mathematical Explorations - Hitoshi Arai, Toshiyuki Kobayashi, Takeshi Saito, Tomohiro Yoshida, accessed July 5, 2025, [https://www.kyoritsu-pub.co.jp/90thmath/math01.html](https://www.kyoritsu-pub.co.jp/90thmath/math01.html) (in Japanese)
[33] ※ Fourier Transform in Excel: Signal Processing and Frequency Analysis Methods ※, accessed July 5, 2025, [https://excelhakase.one/6044/](https://excelhakase.one/6044/) (in Japanese)
[34] Digital Signal Processing ~ Understanding the Discrete Fourier Transform with High School Math ② What is the Fourier Transform? | D-Clue, accessed July 5, 2025, [https://d-clue.com/blog/dsp/dsp2/](https://d-clue.com/blog/dsp/dsp2/) (in Japanese)
[35] Fourier Analysis and Image Processing #Mathematics - Qiita, accessed July 5, 2025, [https://qiita.com/ChiguChigu-Tech/items/f469bf88e2b89fd5b2a0](https://qiita.com/ChiguChigu-Tech/items/f469bf88e2b89fd5b2a0) (in Japanese)
[36] Image Processing in the Frequency Domain, accessed July 5, 2025, [https://www.clg.niigata-u.ac.jp/~medimg/practice_medical_imaging/imgproc_scion/5fourier/index.htm](https://www.clg.niigata-u.ac.jp/~medimg/practice_medical_imaging/imgproc_scion/5fourier/index.htm) (in Japanese)
[37] Image Filtering (Frequency Filtering) for Image Processing Inspection | Visco Technologies Corporation, accessed July 5, 2025, [https://www.visco-tech.com/newspaper/column/detail20/](https://www.visco-tech.com/newspaper/column/detail20/) (in Japanese)
[38] 【Image Processing】2D Fourier Transform and Frequency Filtering - Deliberate Learning, accessed July 5, 2025, [https://tech-deliberate-jiro.com/2dft/](https://tech-deliberate-jiro.com/2dft/) (in Japanese)
[39] What areas of math research are really active / trendy right now. Why? - Reddit, accessed July 5, 2025, [https://www.reddit.com/r/math/comments/112m3ba/what_areas_of_math_research_are_really_active/](https://www.reddit.com/r/math/comments/112m3ba/what_areas_of_math_research_are_really_active/)
[40] Black-Scholes Equation Summary #Python - Qiita, accessed July 5, 2025, [https://qiita.com/N-H-Shimada/items/5c284b8e5c8e26a3a316](https://qiita.com/N-H-Shimada/items/5c284b8e5c8e26a3a316) (in Japanese)
[41] Curves, Surfaces, and Riemannian Manifolds - Hiroshima University, accessed July 5, 2025, [https://www.math.sci.hiroshima-u.ac.jp/tamaru/files/09kika-c.pdf](https://www.math.sci.hiroshima-u.ac.jp/tamaru/files/09kika-c.pdf) (in Japanese)
[42] Introduction to Topological Data Analysis, accessed July 5, 2025, [https://www.chino-js.com/ja/tech/tda/](https://www.chino-js.com/ja/tech/tda/) (in Japanese)
[43] Pure Mathematicians Aim for the Abyss of the World with "Ergodic Group Theory" | Rigakuru - Graduate School of Science and Faculty of Science, The University of Tokyo, accessed July 5, 2025, [https://www.s.u-tokyo.ac.jp/ja/rigakuru/research/9b6gS6T5/](https://www.s.u-tokyo.ac.jp/ja/rigakuru/research/9b6gS6T5/) (in Japanese)
[44] Classification of Groups by Geometric Methods and Applications to Cryptography, accessed July 5, 2025, [https://www.jst.go.jp/kisoken/aip/colab/image/researchers/pdf/111F001_7778_jp.pdf](https://www.jst.go.jp/kisoken/aip/colab/image/researchers/pdf/111F001_7778_jp.pdf) (in Japanese)
[45] List of Mathematics Fields, Detailed Edition ~ From Junior High/High School Math to University Math. Here are some applications. - note, accessed July 5, 2025, [https://note.com/alg_geo/n/n0ff9716ba214](https://note.com/alg_geo/n/n0ff9716ba214) (in Japanese)
[46] History and Development of Graph Theory | nomitake - note, accessed July 5, 2025, [https://note.com/nomitake/n/ne146494d4c85](https://note.com/nomitake/n/ne146494d4c85) (in Japanese)
[47] Graph Theory | 【Practice】Basic Knowledge for Engineers - A Book to Learn Algorithms - Zenn, accessed July 5, 2025, [https://zenn.dev/mandenaren/books/algorithm-study/viewer/study6_graph](https://zenn.dev/mandenaren/books/algorithm-study/viewer/study6_graph) (in Japanese)
[48] Graph Theory: The Science of Relationships | AI Glossary AI Compass, accessed July 5, 2025, [https://ai-compass.weeybrid.co.jp/algorizm/graph-theory-the-science-of-relationships/](https://ai-compass.weeybrid.co.jp/algorizm/graph-theory-the-science-of-relationships/) (in Japanese)
[49] Graph Theory - Wikipedia (Japanese), accessed July 5, 2025, [https://ja.wikipedia.org/wiki/%E3%82%B0%E3%83%A9%E3%83%95%E7%90%86%E8%AB%96](https://ja.wikipedia.org/wiki/%E3%82%B0%E3%83%A9%E3%83%95%E7%90%86%E8%AB%96)
[50] Data Science and Probability | M3M - note, accessed July 5, 2025, [https://note.com/cy_larm/n/n9b51775ba0df](https://note.com/cy_larm/n/n9b51775ba0df) (in Japanese)
[51] Law of Large Numbers and Central Limit Theorem | Library | OPEO Orikawa Professional Engineer Office, accessed July 5, 2025, [https://opeo.jp/library/lecture/tol_anal/basic/ta_lln_cnt/](https://opeo.jp/library/lecture/tol_anal/basic/ta_lln_cnt/) (in Japanese)
[52] Law of Large Numbers and Central Limit Theorem - Saiensu-sha, accessed July 5, 2025, [https://www.saiensu.co.jp/book_support/978-4-7819-1526-5/LectureSlides_Chap5-1-20230110.pdf](https://www.saiensu.co.jp/book_support/978-4-7819-1526-5/LectureSlides_Chap5-1-20230110.pdf) (in Japanese)
[53] 【Understand in 4 Minutes】Explaining the Law of Large Numbers and the Central Limit Theorem! - YouTube, accessed July 5, 2025, [https://www.youtube.com/watch?v=KT2lWxMGfU4](https://www.youtube.com/watch?v=KT2lWxMGfU4) (in Japanese)
[54] Law of Large Numbers and Central Limit Theorem, accessed July 5, 2025, [https://sitmathclub.github.io/research/pdf/2020/omiya/document/siryou_kubota.pdf](https://sitmathclub.github.io/research/pdf/2020/omiya/document/siryou_kubota.pdf) (in Japanese)
[55] Probability/Statistics (for Statistics Test Level 2) 14: Law of Large Numbers and Central Limit Theorem | Buried in Formulas, accessed July 5, 2025, [https://suushikiniumoreru.com/probability14/](https://suushikiniumoreru.com/probability14/) (in Japanese)
[56] Department of Applied Mathematics | Faculty of Science Division I | Education / Faculty and Graduate School | ACADEMICS - Tokyo University of Science, accessed July 5, 2025, [https://www.tus.ac.jp/academics/faculty/sciencedivision1/applied_mathmatics/](https://www.tus.ac.jp/academics/faculty/sciencedivision1/applied_mathmatics/) (in Japanese)
[57] A Defense of "Pure" Mathematics, accessed July 5, 2025, [http://mathsoc.jp/publication/tushin/0101/sunada_sugaku.pdf](http://mathsoc.jp/publication/tushin/0101/sunada_sugaku.pdf) (in Japanese)
[58] Applied Mathematics - Kotobank, accessed July 5, 2025, [https://kotobank.jp/word/%E5%BF%9C%E7%94%A8%E6%95%B0%E5%AD%A6-38911](https://kotobank.jp/word/%E5%BF%9C%E7%94%A8%E6%95%B0%E5%AD%A6-38911) (in Japanese)
[59] Applied Mathematics - Wikipedia (Japanese), accessed July 5, 2025, [https://ja.wikipedia.org/wiki/%E5%BF%9C%E7%94%A8%E6%95%B0%E5%AD%A6](https://ja.wikipedia.org/wiki/%E5%BF%9C%E7%94%A8%E6%95%B0%E5%AD%A6)
[60] Category:Applied mathematics - Wikipedia (Japanese), accessed July 5, 2025, [https://ja.wikipedia.org/wiki/Category:%E5%BF%9C%E7%94%A8%E6%95%B0%E5%AD%A6](https://ja.wikipedia.org/wiki/Category:%E5%BF%9C%E7%94%A8%E6%95%B0%E5%AD%A6)
[61] Mathematics of general relativity - Wikipedia (Japanese), accessed July 5, 2025, [https://ja.wikipedia.org/wiki/%E4%B8%80%E8%88%AC%E7%9B%B8%E5%AF%BE%E6%80%A7%E7%90%86%E8%AB%96%E3%81%AE%E6%95%B0%E5%AD%A6](https://ja.wikipedia.org/wiki/%E4%B8%80%E8%88%AC%E7%9B%B8%E5%AF%BE%E6%80%A7%E7%90%86%E8%AB%96%E3%81%AE%E6%95%B0%E5%AD%A6)
[62] Introduction to Differential Geometry for Gauge Theory and General Relativity - Morikita Publishing, accessed July 5, 2025, [https://www.morikita.co.jp/books/mid/007851](https://www.morikita.co.jp/books/mid/007851) (in Japanese)
[63] Special Feature: The Mathematics of General Relativity (unpublished long version) Hideo Kodama, accessed July 5, 2025, [https://www2.yukawa.kyoto-u.ac.jp/~hideo.kodama/jarticles/GR&Suuri_org_long.pdf](https://www2.yukawa.kyoto-u.ac.jp/~hideo.kodama/jarticles/GR&Suuri_org_long.pdf) (in Japanese)
[64] See Geometry and Surely Understand General Relativity | Gihyo.jp, accessed July 5, 2025, [https://gihyo.jp/book/2022/978-4-297-13040-4](https://gihyo.jp/book/2022/978-4-297-13040-4) (in Japanese)
[65] Differential Geometry and Relativity, accessed July 5, 2025, [http://physmathseminar.web.fc2.com/PDF/differential_geometry_and_theory_of_relativity2.pdf](http://physmathseminar.web.fc2.com/PDF/differential_geometry_and_theory_of_relativity2.pdf) (in Japanese)
[66] General Relativity (1) Analytical Mechanics ~ From a Geometric Perspective ~ (13) - YouTube, accessed July 5, 2025, [https://www.youtube.com/watch?v=jFFwK1mvsN8](https://www.youtube.com/watch?v=jFFwK1mvsN8) (in Japanese)
[67] What are the Navier-Stokes Equations? | CAE Glossary - SimScale, accessed July 5, 2025, [https://simscale.kke.co.jp/caepedia/numerics-background/what-are-the-navier-stokes-equations/](https://simscale.kke.co.jp/caepedia/numerics-background/what-are-the-navier-stokes-equations/)
[68] Dynamical Systems and Stochastic Differential Equations, accessed July 5, 2025, [https://www.s.chiba-u.ac.jp/admission/files/23.pdf](https://www.s.chiba-u.ac.jp/admission/files/23.pdf) (in Japanese)
[69] Navier-Stokes equations - Wikipedia (Japanese), accessed July 5, 2025, [https://ja.wikipedia.org/wiki/%E3%83%8A%E3%83%93%E3%82%A8%E2%80%93%E3%82%B9%E3%83%88%E3%83%BC%E3%82%AF%E3%82%B9%E6%96%B9%E7%A8%8B%E5%BC%8F](https://ja.wikipedia.org/wiki/%E3%83%8A%E3%83%93%E3%82%A8%E2%80%93%E3%82%B9%E3%83%88%E3%83%BC%E3%82%AF%E3%82%B9%E6%96%B9%E7%A8%8B%E5%BC%8F)
[70] On the P vs NP Problem ~ Organizing NP, NP-complete, and NP-hard ~ - Qiita, accessed July 5, 2025, [https://qiita.com/drken/items/5187e49082f7437349c2](https://qiita.com/drken/items/5187e49082f7437349c2) (in Japanese)
[71] The P vs NP Problem for Dummies (The difference between NP-complete and NP-hard), accessed July 5, 2025, [https://www.momoyama-usagi.com/entry/info-p-np](https://www.momoyama-usagi.com/entry/info-p-np) (in Japanese)
[72] Half a Century of P and NP, accessed July 5, 2025, [https://orsj.org/wp-content/corsj/or60-1/or60_1_22.pdf](https://orsj.org/wp-content/corsj/or60-1/or60_1_22.pdf) (in Japanese)
[73] Programming Finite Fields, Part 2: How Reed-Solomon Codes Work #JavaScript - Qiita, accessed July 5, 2025, [https://qiita.com/bellbind/items/b85fe5f5055fc9d42472](https://qiita.com/bellbind/items/b85fe5f5055fc9d42472) (in Japanese)
[74] Understanding Reed-Solomon Codes in 15 Minutes【M3 Tech Talk #187】 - YouTube, accessed July 5, 2025, [https://www.youtube.com/watch?v=q-j1sn0PkRs](https://www.youtube.com/watch?v=q-j1sn0PkRs) (in Japanese)
[75] Fusion Research of Machine Learning and Mathematical Optimization by Manus | moai-lab official - note, accessed July 5, 2025, [https://note.com/moai_lab/n/n3ada57fd5b12](https://note.com/moai_lab/n/n3ada57fd5b12) (in Japanese)
[76] Genre List (Mathematics, Applied Mathematics) - Asakura Publishing, accessed July 5, 2025, [https://www.asakura.co.jp/sgenre_books.php?sgenre_id=13](https://www.asakura.co.jp/sgenre_books.php?sgenre_id=13) (in Japanese)
[77] The Essential Machine Learning Foundations: Math, Probability, Statistics, and Computer Science (Video Collection) - O'Reilly Media, accessed July 5, 2025, [https://www.oreilly.com/library/view/the-essential-machine/9780137903245/](https://www.oreilly.com/library/view/the-essential-machine/9780137903245/)
[78] Mathematics for Machine Learning, accessed July 5, 2025, [https://course.ccs.neu.edu/ds4420sp20/readings/mml-book.pdf](https://course.ccs.neu.edu/ds4420sp20/readings/mml-book.pdf)
[79] Mathematical Foundation for AI and Machine Learning | Data | Video - Packt, accessed July 5, 2025, [https://www.packtpub.com/en-us/product/mathematical-foundation-for-ai-and-machine-learning-9781789613209](https://www.packtpub.com/en-us/product/mathematical-foundation-for-ai-and-machine-learning-9781789613209)
[80] Foundations of Optimization Theory (with practice in Excel, Python, etc.) | Wakara Inc. - Math School for Adults, accessed July 5, 2025, [https://wakara.co.jp/kobetsu/optimization](https://wakara.co.jp/kobetsu/optimization) (in Japanese)
[81] What is Mathematical Optimization? A clear explanation of its differences from Machine Learning/AI and business use cases | DOORS DX, accessed July 5, 2025, [https://www.brainpad.co.jp/doors/contents/about_mathematical_optimization/](https://www.brainpad.co.jp/doors/contents/about_mathematical_optimization/) (in Japanese)
[82] Mathematical Foundation for AI and Machine Learning[Video] - O'Reilly Media, accessed July 5, 2025, [https://www.oreilly.com/library/view/mathematical-foundation-for/9781789613209/](https://www.oreilly.com/library/view/mathematical-foundation-for/9781789613209/)
[83] 1. Mathematical Foundations for Machine Learning, accessed July 5, 2025, [https://japan-medical-ai.github.io/medical-ai-course-materials/notebooks/01_Basic_Math_for_ML.html](https://japan-medical-ai.github.io/medical-ai-course-materials/notebooks/01_Basic_Math_for_ML.html) (in Japanese)
[84] Mathematics for Machine Learning / Deisenroth, Marc Peter / Faisal - Kinokuniya, accessed July 5, 2025, [https://www.kinokuniya.co.jp/f/dsg-01-9784320125810](https://www.kinokuniya.co.jp/f/dsg-01-9784320125810) (in Japanese)
[85] MATHEMATICAL FOUNDATIONS OF MACHINE LEARNING: Unveiling the Mathematical Essence of Machine Learning (2024 Guide for Beginners) by DAVID MACKAY | eBook | Barnes & Noble®, accessed July 5, 2025, [https://www.barnesandnoble.com/w/mathematical-foundations-of-machine-learning-david-mackay/1145009428](https://www.barnesandnoble.com/w/mathematical-foundations-of-machine-learning-david-mackay/1145009428)
[86] Topological Data Analysis and its Application Examples - Speaker Deck, accessed July 5, 2025, [https://speakerdeck.com/brainpadpr/wei-xiang-de-detajie-xi-tosonoying-yong-li](https://speakerdeck.com/brainpadpr/wei-xiang-de-detajie-xi-tosonoying-yong-li) (in Japanese)
[87] The Present State of Topological Data Analysis - RIMS, Kyoto University, accessed July 5, 2025, [https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2057-05.pdf](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2057-05.pdf) (in Japanese)
[88] Introducing Topological Data Analysis - Shinonome Tech Blog, accessed July 5, 2025, [http://blog.shinonome.io/wei-xiang/](http://blog.shinonome.io/wei-xiang/) (in Japanese)
[89] Foundations and Applications of Topological Data Analysis - (AIMR), Tohoku University, accessed July 5, 2025, [https://www.wpi-aimr.tohoku.ac.jp/hiraoka_labo/introduction_j.pdf](https://www.wpi-aimr.tohoku.ac.jp/hiraoka_labo/introduction_j.pdf) (in Japanese)
[90] The Next-Generation Data Analysis Revolution: From the Basics to the Forefront of Topological Data Analysis (TDA) | Reinforz.ai, accessed July 5, 2025, [https://ai.reinforz.co.jp/989](https://ai.reinforz.co.jp/989) (in Japanese)
[91] Black-Scholes Equation - TANAAKK, accessed July 5, 2025, [https://www.tanaakk.com/2025/03/18/black-scholes-equation/](https://www.tanaakk.com/2025/03/18/black-scholes-equation/)
[92] Black–Scholes equation - Wikipedia, accessed July 5, 2025, [https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_equation](https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_equation)
[93] Black-Scholes Model (BS Formula) - Financial Keyword Explanations - Sigma Investment School, accessed July 5, 2025, [https://www.sigmabase.co.jp/useful/keyword/h/bs_model.html](https://www.sigmabase.co.jp/useful/keyword/h/bs_model.html) (in Japanese)
[94] Theory and Python Implementation of the Black-Scholes Equation - Qiita, accessed July 5, 2025, [https://qiita.com/yotapoon/items/30c1bc411c5a8f08d219](https://qiita.com/yotapoon/items/30c1bc411c5a8f08d219) (in Japanese)
[95] A Quick Understanding of the "Black-Scholes Model" | Bespoke Partner Co., Ltd. - note, accessed July 5, 2025, [https://note.com/bespokepartner/n/nbfde7c5e140d](https://note.com/bespokepartner/n/nbfde7c5e140d) (in Japanese)
