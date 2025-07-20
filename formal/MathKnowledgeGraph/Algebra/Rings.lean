/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.Int
import Mathlib.Data.ZMod.Basic

/-!
# Rings and Fields

This file contains basic definitions and theorems about rings and fields,
corresponding to the content in our knowledge graph.

## Main definitions

* `Ring` - A set with two binary operations satisfying ring axioms (from Mathlib)
* `Field` - A commutative ring where every non-zero element has a multiplicative inverse
* Examples of rings and fields

## References

* Node ID: def-ring
* Quarto file: content/algebra/def-ring.qmd
* Lean ID: Mathlib.Algebra.Ring.Defs.Ring

* Node ID: def-field
* Quarto file: content/algebra/def-field.qmd
* Lean ID: Mathlib.Algebra.Field.Defs.Field
-/

namespace MathKnowledgeGraph
namespace Algebra

section RingDefinitions

/--
A ring is a set with two binary operations (+ and *) satisfying:
1. (R, +) is an abelian group
2. Multiplication is associative
3. Distributivity holds

This corresponds to def-ring in our knowledge graph.

Node ID: def-ring
-/
-- Note: Mathlib's Ring typeclass already captures this definition
-- We'll demonstrate the properties and provide examples

/-- The additive group structure of a ring -/
theorem ring_add_group {R : Type*} [Ring R] : AddCommGroup R := inferInstance

/-- Multiplication in a ring is associative -/
theorem ring_mul_assoc {R : Type*} [Ring R] (a b c : R) : (a * b) * c = a * (b * c) := by
  exact mul_assoc a b c

/-- Left distributivity in a ring -/
theorem ring_left_distrib {R : Type*} [Ring R] (a b c : R) : a * (b + c) = a * b + a * c := by
  exact mul_add a b c

/-- Right distributivity in a ring -/
theorem ring_right_distrib {R : Type*} [Ring R] (a b c : R) : (a + b) * c = a * c + b * c := by
  exact add_mul a b c

/-- Zero is absorbing for multiplication -/
theorem ring_zero_mul {R : Type*} [Ring R] (a : R) : 0 * a = 0 := by
  exact zero_mul a

theorem ring_mul_zero {R : Type*} [Ring R] (a : R) : a * 0 = 0 := by
  exact mul_zero a

end RingDefinitions

section RingExamples

/-- The integers form a ring under addition and multiplication -/
example : Ring ℤ := inferInstance

/-- The n×n matrices over a ring form a ring -/
example {n : ℕ} {R : Type*} [Ring R] : Ring (Matrix (Fin n) (Fin n) R) := inferInstance

/-- Polynomials over a ring form a ring -/
example {R : Type*} [Ring R] : Ring (Polynomial R) := inferInstance

/-- The integers modulo n form a ring -/
example {n : ℕ} [NeZero n] : Ring (ZMod n) := inferInstance

end RingExamples

section FieldDefinitions

/--
A field is a commutative ring where every non-zero element has a multiplicative inverse.
Equivalently, (F, +) is an abelian group and (F \ {0}, *) is an abelian group.

This corresponds to def-field in our knowledge graph.

Node ID: def-field
-/
-- Note: Mathlib's Field typeclass captures this definition

/-- Every field is a commutative ring -/
theorem field_is_comm_ring {F : Type*} [Field F] : CommRing F := inferInstance

/-- In a field, every non-zero element has an inverse -/
theorem field_inv_exists {F : Type*} [Field F] (a : F) (ha : a ≠ 0) :
  ∃ b : F, a * b = 1 := by
  use a⁻¹
  exact mul_inv_cancel ha

/-- In a field, there are no zero divisors -/
theorem field_no_zero_divisors {F : Type*} [Field F] (a b : F) (h : a * b = 0) :
  a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · left
    exact ha
  · right
    have h' : a⁻¹ * (a * b) = a⁻¹ * 0 := by rw [h]
    rw [← mul_assoc, inv_mul_cancel ha, one_mul, mul_zero] at h'
    exact h'

/-- The multiplicative group of non-zero elements in a field -/
def field_units_group (F : Type*) [Field F] : CommGroup Fˣ := inferInstance

end FieldDefinitions

section FieldExamples

/-- The rational numbers form a field -/
example : Field ℚ := inferInstance

/-- The real numbers form a field -/
example : Field ℝ := inferInstance

/-- The complex numbers form a field -/
example : Field ℂ := inferInstance

/-- The integers modulo a prime p form a field -/
example {p : ℕ} [Fact p.Prime] : Field (ZMod p) := inferInstance

/-- Example: In a field, division by non-zero elements is well-defined -/
theorem field_div_well_defined {F : Type*} [Field F] (a b : F) (hb : b ≠ 0) :
  ∃! c : F, b * c = a := by
  use a / b
  constructor
  · field_simp [hb]
  · intro y hy
    have h : b * (a / b) = b * y := by
      rw [mul_div_cancel' a hb]
      exact hy
    exact mul_left_cancel₀ hb h

end FieldExamples

section RingFieldRelationships

/-- Every field is an integral domain (commutative ring with no zero divisors) -/
theorem field_is_integral_domain {F : Type*} [Field F] : IsDomain F := inferInstance

/-- Not every ring is a field - example: integers -/
theorem int_not_field : ¬(∃ (_ : Field ℤ), True) := by
  intro ⟨h, _⟩
  -- In a field, 2 must have an inverse
  have : ∃ b : ℤ, (2 : ℤ) * b = 1 := field_inv_exists 2 (by norm_num : (2 : ℤ) ≠ 0)
  obtain ⟨b, hb⟩ := this
  -- But no integer b satisfies 2 * b = 1
  have : (2 : ℤ) * b = 2 * b := rfl
  rw [hb] at this
  -- This would mean 2 * b = 1, but 2 * b is even and 1 is odd
  have : Even (2 * b) := Even.intro_left b rfl
  rw [this] at hb
  exact Int.odd_one_iff_not_even.mp trivial (even_iff_not_odd.mpr hb)

end RingFieldRelationships

end Algebra
end MathKnowledgeGraph
