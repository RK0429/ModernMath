/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Basic Topology

This file contains basic definitions and theorems about topological spaces,
corresponding to the content in our knowledge graph.

## Main definitions

* `TopologicalSpace` - A set with a topology (from Mathlib)
* Open sets and their properties

## References

* Node ID: def-topological-space, def-open-set
* Quarto file: content/topology/def-topological-space.qmd
* Theorem: thm-union-open-sets
-/

namespace MathKnowledgeGraph
namespace Topology

section OpenSets

variable {X : Type*} [TopologicalSpace X]

/-- The union of any collection of open sets is open -/
theorem union_of_open_is_open {ι : Type*} {U : ι → Set X} 
    (hU : ∀ i, IsOpen (U i)) : IsOpen (⋃ i, U i) := by
  exact isOpen_iUnion hU

/-- The intersection of two open sets is open -/
theorem inter_of_open_is_open {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : IsOpen (A ∩ B) := by
  exact IsOpen.inter hA hB

/-- Example: In ℝ, open intervals are open sets -/
example (a b : ℝ) : IsOpen {x : ℝ | a < x ∧ x < b} := by
  exact isOpen_Ioo

end OpenSets

section CompactSpaces

variable {X : Type*} [TopologicalSpace X]

/-- Example of a compact set: closed intervals in ℝ are compact -/
example (a b : ℝ) : IsCompact {x : ℝ | a ≤ x ∧ x ≤ b} := by
  exact isCompact_Icc

end CompactSpaces

end Topology
end MathKnowledgeGraph