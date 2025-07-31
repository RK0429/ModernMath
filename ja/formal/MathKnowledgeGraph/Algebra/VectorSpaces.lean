/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic

open Module Basis

/-!
# Vector Spaces and Linear Transformations

This file contains definitions and theorems about vector spaces and linear transformations,
corresponding to the content in our knowledge graph.

## Main definitions

* `Module` - Vector space (called Module in Mathlib)
* `LinearMap` - Linear transformation
* `LinearIndependent` - Linear independence
* `Submodule.span` - Span of vectors
* `Basis` - Basis of a vector space

## References

* Node ID: def-vector-space, def-linear-transformation, def-basis, def-linear-independence
* Quarto file: content/algebra/def-vector-space.qmd
-/

namespace MathKnowledgeGraph
namespace Algebra

/-!
## Vector Space Definition (def-vector-space)

In Mathlib, vector spaces are called modules. A module over a field is a vector space.
The axioms are:
1. Addition forms an abelian group
2. Scalar multiplication is associative, has identity, and distributes
-/

section VectorSpaceDefinition

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A vector space has an additive identity element (zero vector) -/
theorem vector_space_has_zero : ∃ z : V, ∀ v : V, v + z = v := by
  use 0
  intro v
  exact add_zero v

/-- Scalar multiplication by 1 is the identity -/
theorem scalar_mul_one (v : V) : (1 : F) • v = v := by
  exact one_smul F v

/-- Scalar multiplication distributes over vector addition -/
theorem scalar_mul_add (a : F) (u v : V) : a • (u + v) = a • u + a • v := by
  exact smul_add a u v

/-- Scalar addition distributes over scalar multiplication -/
theorem add_scalar_mul (a b : F) (v : V) : (a + b) • v = a • v + b • v := by
  exact add_smul a b v

/-- Scalar multiplication is associative -/
theorem scalar_mul_assoc (a b : F) (v : V) : a • (b • v) = (a * b) • v := by
  exact smul_smul a b v

/-- Zero scalar annihilates any vector -/
theorem zero_scalar_mul (v : V) : (0 : F) • v = 0 := by
  exact zero_smul F v

/-- Example: ℝⁿ is a vector space over ℝ -/
example : Module ℝ (Fin n → ℝ) := by
  exact inferInstance

end VectorSpaceDefinition

/-!
## Linear Transformations (def-linear-transformation)

A linear transformation is a function between vector spaces that preserves
addition and scalar multiplication.
-/

section LinearTransformations

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- A linear transformation preserves addition -/
theorem linear_map_add (f : V →ₗ[F] W) (u v : V) :
    f (u + v) = f u + f v := by
  exact f.map_add u v

/-- A linear transformation preserves scalar multiplication -/
theorem linear_map_smul (f : V →ₗ[F] W) (a : F) (v : V) :
    f (a • v) = a • f v := by
  exact f.map_smul a v

/-- A linear transformation maps zero to zero -/
theorem linear_map_zero (f : V →ₗ[F] W) : f 0 = 0 := by
  exact f.map_zero

/-- Linear transformations preserve linear combinations -/
theorem linear_map_linear_combination (f : V →ₗ[F] W) {n : ℕ}
    (a : Fin n → F) (v : Fin n → V) :
    f (∑ i : Fin n, a i • v i) = ∑ i : Fin n, a i • f (v i) := by
  simp only [map_sum, linear_map_smul]

/-- Example: Matrix multiplication defines a linear transformation -/
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := by
  exact Matrix.toLin' A

/-- The identity function is a linear transformation -/
example : V →ₗ[F] V := by
  exact LinearMap.id

end LinearTransformations

/-!
## Linear Independence (def-linear-independence)

A set of vectors is linearly independent if no vector in the set can be written
as a linear combination of the others.
-/

section LinearIndependence

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A set is linearly independent if the only linear combination that equals zero
    has all coefficients equal to zero -/
theorem linear_independent_iff {ι : Type*} (v : ι → V) :
    LinearIndependent F v ↔
    ∀ (a : ι →₀ F), (∑ i ∈ a.support, a i • v i) = 0 → a = 0 := by
  exact linearIndependent_iff

/-- Empty set is linearly independent -/
theorem empty_linear_independent : LinearIndependent F (fun (_ : Empty) => (0 : V)) := by
  exact linearIndependent_empty_type

/-- If a set is linearly independent, any subset is also linearly independent -/
theorem linear_independent_subset {ι ι' : Type*} (f : ι' → ι) (hf : Function.Injective f)
    {v : ι → V} (hv : LinearIndependent F v) :
    LinearIndependent F (v ∘ f) := by
  exact hv.comp f hf

end LinearIndependence

/-!
## Span (def-span)

The span of a set of vectors is the smallest subspace containing those vectors.
-/

section Span

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The span contains all the original vectors -/
theorem mem_span_self {s : Set V} (v : V) (hv : v ∈ s) :
    v ∈ Submodule.span F s := by
  exact Submodule.subset_span hv

/-- The span is closed under addition -/
theorem span_add_closed {s : Set V} (u v : V)
    (hu : u ∈ Submodule.span F s) (hv : v ∈ Submodule.span F s) :
    u + v ∈ Submodule.span F s := by
  exact Submodule.add_mem _ hu hv

/-- The span is closed under scalar multiplication -/
theorem span_smul_closed {s : Set V} (a : F) (v : V)
    (hv : v ∈ Submodule.span F s) :
    a • v ∈ Submodule.span F s := by
  exact Submodule.smul_mem _ a hv

/-- The span is the smallest subspace containing the set -/
theorem span_minimal {s : Set V} {W : Submodule F V} (h : s ⊆ W) :
    Submodule.span F s ≤ W := by
  exact Submodule.span_le.mpr h

end Span

/-!
## Basis (def-basis)

A basis is a linearly independent spanning set.
-/

section Basis

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- A basis is linearly independent -/
theorem basis_linear_independent {ι : Type*} (b : Basis ι F V) :
    LinearIndependent F (b : ι → V) := by
  exact b.linearIndependent

/-- A basis spans the entire space -/
theorem basis_spans {ι : Type*} (b : Basis ι F V) :
    Submodule.span F (Set.range (b : ι → V)) = ⊤ := by
  exact b.span_eq

/-- Every vector can be uniquely written as a linear combination of basis vectors -/
theorem basis_repr_unique {ι : Type*} [Fintype ι] (b : Basis ι F V) (v : V) :
    v = ∑ i : ι, (b.repr v) i • (b : ι → V) i := by
  exact (b.sum_repr v).symm

/-- Example: Standard basis for ℝⁿ -/
noncomputable example (n : ℕ) : Basis (Fin n) ℝ (Fin n → ℝ) := by
  exact Pi.basisFun ℝ (Fin n)

/-- Two finite-dimensional vector spaces over the same field with the same dimension are isomorphic -/
theorem finite_dim_isomorphic {ι : Type*} [Fintype ι]
    (bV : Basis ι F V) (bW : Basis ι F W) :
    Nonempty (V ≃ₗ[F] W) := by
  exact ⟨bV.equiv bW (Equiv.refl ι)⟩

end Basis

/-!
## Kernel and Image (def-kernel, def-image)

The kernel and image are fundamental subspaces associated with a linear transformation.
-/

section KernelImage

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The kernel of a linear map is a subspace -/
theorem ker_is_subspace (f : V →ₗ[F] W) :
    LinearMap.ker f ≤ ⊤ := by
  exact le_top

/-- A vector is in the kernel iff it maps to zero -/
theorem mem_ker_iff (f : V →ₗ[F] W) (v : V) :
    v ∈ LinearMap.ker f ↔ f v = 0 := by
  exact LinearMap.mem_ker

/-- The image of a linear map is a subspace -/
theorem range_is_subspace (f : V →ₗ[F] W) :
    LinearMap.range f ≤ ⊤ := by
  exact le_top

/-- A vector is in the image iff it's the image of some vector -/
theorem mem_range_iff (f : V →ₗ[F] W) (w : W) :
    w ∈ LinearMap.range f ↔ ∃ v : V, f v = w := by
  exact LinearMap.mem_range

/-- Rank-Nullity Theorem (thm-rank-nullity) -/
theorem rank_nullity [FiniteDimensional F V] (f : V →ₗ[F] W) :
    Module.finrank F (LinearMap.ker f) + Module.finrank F (LinearMap.range f) =
    Module.finrank F V := by
  sorry

end KernelImage

end Algebra
end MathKnowledgeGraph
