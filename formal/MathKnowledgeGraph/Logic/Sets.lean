/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

/-!
# Sets and Basic Logic

This file contains basic definitions and theorems about sets,
corresponding to the content in our knowledge graph.

## Main definitions

* `Set` - The type of sets (imported from Mathlib)
* Basic set operations: union, intersection, complement

## References

* Node ID: def-set
* Quarto file: content/logic-set-theory/def-set.qmd
-/

namespace MathKnowledgeGraph
namespace Logic

-- Example: Basic set operations and properties
section SetOperations

variable {α : Type*} (A B C : Set α)

/-- The union of two sets contains all elements from either set -/
theorem union_contains_both : A ⊆ A ∪ B ∧ B ⊆ A ∪ B := by
  constructor
  · exact Set.subset_union_left
  · exact Set.subset_union_right

/-- The intersection of two sets is contained in both sets -/
theorem inter_subset_both : A ∩ B ⊆ A ∧ A ∩ B ⊆ B := by
  constructor
  · exact Set.inter_subset_left
  · exact Set.inter_subset_right

/-- Distributivity of union over intersection -/
theorem union_distrib_inter : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff]
  tauto

end SetOperations

end Logic
end MathKnowledgeGraph