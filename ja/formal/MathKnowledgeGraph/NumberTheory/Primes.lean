/-
Copyright (c) 2025 Math Knowledge Graph Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Knowledge Graph Contributors
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

/-!
# Prime Numbers

This file contains basic definitions and theorems about prime numbers,
corresponding to the content in our knowledge graph.

## Main definitions

* `Prime` - Definition of prime numbers (from Mathlib)
* Basic properties of primes

## References

* Node ID: def-prime-number
* Quarto file: content/number-theory/def-prime-number.qmd
* Theorem: thm-fundamental-arithmetic
-/

namespace MathKnowledgeGraph
namespace NumberTheory

section PrimeNumbers

/-- 2 is a prime number -/
example : Nat.Prime 2 := by
  exact Nat.prime_two

/-- 3 is a prime number -/
example : Nat.Prime 3 := by
  exact Nat.prime_three

/-- Example: If p is prime and p divides a product, then p divides one of the factors -/
theorem prime_divides_product {p a b : ℕ} (hp : Nat.Prime p)
    (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  exact hp.dvd_mul.mp h

/-- 4 is not prime -/
example : ¬ Nat.Prime 4 := by
  intro h
  have h_div : 2 ∣ 4 := by norm_num
  have h_lt : 2 < 4 := by norm_num
  have h_ne : 2 ≠ 1 := by norm_num
  have : 2 = 1 ∨ 2 = 4 := h.eq_one_or_self_of_dvd 2 h_div
  cases this with
  | inl h1 => exact h_ne h1
  | inr h2 => norm_num at h2

end PrimeNumbers

section Induction

/-- Mathematical induction principle (already in Lean's foundation) -/
theorem math_induction (P : ℕ → Prop)
    (base : P 0)
    (step : ∀ n, P n → P (n + 1)) :
    ∀ n, P n := by
  exact Nat.rec base step

/-- Example use of induction: 0 + 1 + ... + n = n(n+1)/2 -/
theorem sum_formula (n : ℕ) : 2 * (Finset.range n).sum (·+1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

end Induction

end NumberTheory
end MathKnowledgeGraph
