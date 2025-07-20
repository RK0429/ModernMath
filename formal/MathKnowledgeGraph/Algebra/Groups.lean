/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic

/-!
# Groups

This file contains basic definitions and theorems about groups,
corresponding to the content in our knowledge graph.

## Main definitions

* `Group` - A set with a binary operation satisfying group axioms (from Mathlib)
* Examples of groups

## References

* Node ID: def-group
* Quarto file: content/algebra/def-group.qmd
* Lean ID: Mathlib.Algebra.Group.Defs.Group
-/

namespace MathKnowledgeGraph
namespace Algebra

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