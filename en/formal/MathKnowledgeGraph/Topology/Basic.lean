/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Connected.Basic

/-!
# Basic Topology

This file contains basic definitions and theorems about topological spaces,
corresponding to the content in our knowledge graph.

## Main definitions

* `TopologicalSpace` - A set with a topology (from Mathlib)
* Open sets and their properties
* Closed sets and their properties
* Compact spaces and the Hausdorff property

## References

* Node ID: def-topological-space, def-open-set, def-closed-set, def-compact, def-hausdorff
* Quarto file: content/topology/def-topological-space.qmd
* Theorem: thm-union-open-sets, thm-metric-hausdorff
-/

namespace MathKnowledgeGraph
namespace Topology

/-!
## Topological Space Definition (def-topological-space)

A topological space is formalized in Mathlib as a type class `TopologicalSpace X`.
The axioms are:
1. The empty set and whole space are open
2. Arbitrary unions of open sets are open
3. Finite intersections of open sets are open
-/

section TopologicalSpaceDefinition

variable {X : Type*} [TopologicalSpace X]

/-- The empty set is open in any topological space -/
theorem empty_is_open : IsOpen (∅ : Set X) := by
  exact isOpen_empty

/-- The whole space is open in any topological space -/
theorem univ_is_open : IsOpen (Set.univ : Set X) := by
  exact isOpen_univ

/-- Proof that topological spaces satisfy the axioms from def-topological-space -/
theorem topology_axioms :
    (IsOpen (∅ : Set X)) ∧
    (IsOpen (Set.univ : Set X)) ∧
    (∀ {ι : Type*} {U : ι → Set X}, (∀ i, IsOpen (U i)) → IsOpen (⋃ i, U i)) ∧
    (∀ {A B : Set X}, IsOpen A → IsOpen B → IsOpen (A ∩ B)) := by
  constructor
  · exact isOpen_empty
  constructor
  · exact isOpen_univ
  constructor
  · intros ι U hU
    exact isOpen_iUnion hU
  · intros A B hA hB
    exact IsOpen.inter hA hB

end TopologicalSpaceDefinition

/-!
## Open Sets (def-open-set)

Open sets are the elements of the topology τ. In Mathlib, a set is open
if it satisfies the predicate `IsOpen`.
-/

section OpenSets

variable {X : Type*} [TopologicalSpace X]

/-- The union of any collection of open sets is open (thm-union-open-sets) -/
theorem union_of_open_is_open {ι : Type*} {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) : IsOpen (⋃ i, U i) := by
  exact isOpen_iUnion hU

/-- The intersection of two open sets is open -/
theorem inter_of_open_is_open {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : IsOpen (A ∩ B) := by
  exact IsOpen.inter hA hB

/-- The intersection of finitely many open sets is open -/
theorem finite_inter_of_open_is_open {ι : Type*} [Fintype ι] {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) : IsOpen (⋂ i, U i) := by
  exact isOpen_iInter_of_finite hU

-- Example: In ℝ, open intervals are open sets
-- example (a b : ℝ) : IsOpen {x : ℝ | a < x ∧ x < b} := by
--   exact isOpen_Ioo

-- Example: In a discrete space, every set is open
-- Note: DiscreteTopology requires additional imports
-- example {X : Type*} [DiscreteTopology X] (A : Set X) : IsOpen A := by
--   simp only [isOpen_discrete]

end OpenSets

/-!
## Closed Sets (def-closed-set)

Closed sets are complements of open sets.
-/

section ClosedSets

variable {X : Type*} [TopologicalSpace X]

/-- A set is closed if and only if its complement is open -/
theorem closed_iff_compl_open {A : Set X} : IsClosed A ↔ IsOpen Aᶜ := by
  -- By definition, a set is closed iff its complement is open
  exact isOpen_compl_iff.symm

/-- The empty set is closed -/
theorem empty_is_closed : IsClosed (∅ : Set X) := by
  exact isClosed_empty

/-- The whole space is closed -/
theorem univ_is_closed : IsClosed (Set.univ : Set X) := by
  exact isClosed_univ

/-- The intersection of any collection of closed sets is closed -/
theorem inter_of_closed_is_closed {ι : Type*} {C : ι → Set X}
    (hC : ∀ i, IsClosed (C i)) : IsClosed (⋂ i, C i) := by
  exact isClosed_iInter hC

/-- The union of two closed sets is closed -/
theorem union_of_closed_is_closed {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) : IsClosed (A ∪ B) := by
  exact IsClosed.union hA hB

end ClosedSets

/-!
## Compact Spaces (def-compact)

A topological space is compact if every open cover has a finite subcover.
-/

section CompactSpaces

variable {X : Type*} [TopologicalSpace X]

-- Example of a compact set: closed intervals in ℝ are compact (Heine-Borel theorem)
-- Note: This requires additional imports for interval notation
-- theorem closed_interval_compact (a b : ℝ) : IsCompact {x : ℝ | a ≤ x ∧ x ≤ b} := by
--   exact isCompact_Icc

/-- In a compact space, every closed subset is compact -/
theorem closed_subset_of_compact_is_compact {K : Set X} [CompactSpace X]
    (hK : IsClosed K) : IsCompact K := by
  exact hK.isCompact

end CompactSpaces

/-!
## Hausdorff Spaces (def-hausdorff)

A topological space is Hausdorff if any two distinct points have disjoint open neighborhoods.
-/

section HausdorffSpaces

variable {X : Type*} [TopologicalSpace X]

/-- Every metric space is Hausdorff (thm-metric-hausdorff) -/
theorem metric_space_is_hausdorff {X : Type*} [MetricSpace X] : T2Space X := by
  -- This is an instance in Mathlib
  exact inferInstance

/-- In a Hausdorff space, singletons are closed -/
theorem singleton_closed_in_hausdorff [T2Space X] (x : X) : IsClosed {x} := by
  exact isClosed_singleton

/-- In a Hausdorff space, compact sets are closed -/
theorem compact_closed_in_hausdorff [T2Space X] {K : Set X} (hK : IsCompact K) : IsClosed K := by
  exact hK.isClosed

end HausdorffSpaces

/-!
## Connected Spaces (def-connected)

A topological space is connected if it cannot be written as a union of two disjoint non-empty open sets.
-/

section ConnectedSpaces

variable {X : Type*} [TopologicalSpace X]

-- The real line is connected
-- Note: This requires the ConnectedSpace instance for ℝ which needs additional imports
-- theorem real_line_connected : IsConnected (Set.univ : Set ℝ) := by
--   haveI : ConnectedSpace ℝ := inferInstance
--   exact isConnected_univ

/-- The continuous image of a connected set is connected -/
theorem continuous_image_of_connected {Y : Type*} [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} (hA : IsConnected A) :
    IsConnected (f '' A) := by
  exact IsConnected.image hA f hf.continuousOn

end ConnectedSpaces

end Topology
end MathKnowledgeGraph
