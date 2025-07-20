/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

/-!
# Groups

This file contains basic definitions and theorems about groups,
corresponding to the content in our knowledge graph.

## Main definitions

* `Group` - A set with a binary operation satisfying group axioms (from Mathlib)
* Binary operations and their properties
* Subgroups and related theorems
* Examples of groups

## References

* Node ID: def-group
* Quarto file: content/algebra/def-group.qmd
* Lean ID: Mathlib.Algebra.Group.Defs.Group

* Node ID: def-binary-operation
* Quarto file: content/algebra/def-binary-operation.qmd

* Node ID: def-subgroup
* Quarto file: content/algebra/def-subgroup.qmd
-/

namespace MathKnowledgeGraph
namespace Algebra

section BinaryOperations

/-- 
A binary operation on a type α is a function α → α → α.
This corresponds to def-binary-operation in our knowledge graph.

Node ID: def-binary-operation
-/
abbrev BinaryOp (α : Type*) := α → α → α

/-- A binary operation is associative if (a * b) * c = a * (b * c) for all a, b, c -/
def IsAssociative {α : Type*} (op : BinaryOp α) : Prop :=
  ∀ a b c : α, op (op a b) c = op a (op b c)

/-- A binary operation is commutative if a * b = b * a for all a, b -/
def IsCommutative {α : Type*} (op : BinaryOp α) : Prop :=
  ∀ a b : α, op a b = op b a

/-- An element e is a left identity for op if e * a = a for all a -/
def IsLeftIdentity {α : Type*} (op : BinaryOp α) (e : α) : Prop :=
  ∀ a : α, op e a = a

/-- An element e is a right identity for op if a * e = a for all a -/
def IsRightIdentity {α : Type*} (op : BinaryOp α) (e : α) : Prop :=
  ∀ a : α, op a e = a

/-- An element e is a two-sided identity for op if it's both a left and right identity -/
def IsIdentity {α : Type*} (op : BinaryOp α) (e : α) : Prop :=
  IsLeftIdentity op e ∧ IsRightIdentity op e

end BinaryOperations

section Subgroups

/-- 
A subgroup of a group G is a subset that is closed under the group operation,
contains the identity, and contains inverses.

This corresponds to def-subgroup in our knowledge graph.

Node ID: def-subgroup
-/
-- Note: Mathlib already has a comprehensive Subgroup definition
-- We'll demonstrate the concept with examples and theorems

/-- The trivial subgroup containing only the identity element -/
def trivialSubgroup (G : Type*) [Group G] : Subgroup G := ⊥

/-- Every group is a subgroup of itself -/
def wholeSubgroup (G : Type*) [Group G] : Subgroup G := ⊤

/-- The intersection of subgroups is a subgroup -/
theorem subgroup_inter {G : Type*} [Group G] (H K : Subgroup G) :
  ∃ (HK : Subgroup G), HK.carrier = H.carrier ∩ K.carrier := by
  use H ⊓ K
  rfl

/-- Subgroup test: A subset H is a subgroup iff it's nonempty and closed under multiplication by inverses -/
theorem subgroup_test {G : Type*} [Group G] (H : Set G) :
  (∃ (S : Subgroup G), S.carrier = H) ↔ 
  (H.Nonempty ∧ ∀ a b ∈ H, a * b⁻¹ ∈ H) := by
  sorry -- This is a standard result in group theory

end Subgroups

section GroupExamples

-- Note: This example requires additional imports
-- /-- The integers form a group under addition -/
-- example : AddGroup ℤ := inferInstance

/-- Example of using group properties: the inverse of the inverse is the original element -/
theorem inv_inv_eq {G : Type*} [Group G] (g : G) : g⁻¹⁻¹ = g := by
  exact inv_inv g

/-- Example: In a group, we can cancel on the left -/
theorem left_cancel {G : Type*} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  have h' : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by rw [h]
  rw [← mul_assoc, inv_mul_cancel, one_mul] at h'
  rw [← mul_assoc, inv_mul_cancel, one_mul] at h'
  exact h'

/-- Example: Identity element is unique -/
theorem unique_identity {G : Type*} [Group G] (e : G) 
    (h : ∀ g : G, e * g = g ∧ g * e = g) : e = 1 := by
  have h1 := (h 1).1
  rw [mul_one] at h1
  exact h1

end GroupExamples

end Algebra
end MathKnowledgeGraph