/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

/-!
# Limits and Continuity

This file contains basic definitions and theorems about limits and continuity,
corresponding to the content in our knowledge graph.

## Main definitions

* Limits of functions
* Continuity

## References

* Node ID: def-limit, def-continuity
* Quarto file: content/analysis/def-limit.qmd, content/analysis/def-continuity.qmd
* Theorem: thm-arithmetic-limits
-/

namespace MathKnowledgeGraph
namespace Analysis

open Filter Topology

section Limits

/-- Example: The limit of x² as x approaches 2 is 4 -/
example : Filter.Tendsto (fun x : ℝ => x^2) (𝓝 2) (𝓝 4) := by
  rw [show (4 : ℝ) = 2^2 by norm_num]
  exact Continuous.tendsto (continuous_pow 2) 2

/-- Example: Sum of limits equals limit of sum -/
theorem limit_add {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : Filter.Tendsto f (𝓝 a) (𝓝 L))
    (hg : Filter.Tendsto g (𝓝 a) (𝓝 M)) :
    Filter.Tendsto (fun x => f x + g x) (𝓝 a) (𝓝 (L + M)) := by
  exact Filter.Tendsto.add hf hg

/-- Example: Product of limits equals limit of product -/
theorem limit_mul {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : Filter.Tendsto f (𝓝 a) (𝓝 L))
    (hg : Filter.Tendsto g (𝓝 a) (𝓝 M)) :
    Filter.Tendsto (fun x => f x * g x) (𝓝 a) (𝓝 (L * M)) := by
  exact Filter.Tendsto.mul hf hg

end Limits

section Continuity

/-- Example: Polynomial functions are continuous -/
example : Continuous (fun x : ℝ => x^3 - 2*x + 1) := by
  continuity

/-- Example: The composition of continuous functions is continuous -/
theorem continuous_comp {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f (g x)) := by
  exact Continuous.comp hf hg

end Continuity

end Analysis
end MathKnowledgeGraph
