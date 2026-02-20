/-
  Proofs of selected theorems in chapter 1

-/

import Mathlib.Tactic

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

set_option linter.style.commandStart false

open Complex

noncomputable section Complex_field

-- Find the real and imaginary part of 3-5i
#eval Complex.re (3 - 5*I)
#eval Complex.im (3 - 5*I)

-- Find the real and imaginary part of 7
#eval Complex.re (7)
#eval Complex.im (7)


end Complex_field


section imaginary_parts

def is_purely_imaginary (z : ℂ) : Prop :=
  re z = 0

example (a : ℝ) : is_purely_imaginary ⟨0, a⟩ := by
  unfold is_purely_imaginary
  rfl

-- Fuchs Example 10.2.6
-- Prove that (a + ai)^2 is purely imaginary
example (a : ℝ) : is_purely_imaginary (⟨a, a⟩^2) := by
  unfold is_purely_imaginary
  have h : ( (Complex.mk a a)^2 ).re = a*a - a*a := by
    simp [pow_two]
  simp [h]


end imaginary_parts




section linear_equation

example (z : ℂ) : 5*z = I →  z = (1/5)*I := by
  intro h
  rw [mul_comm 5 z] at h

  -- isolate z
  have h1 : z = I/5 := by
    apply (eq_div_iff_mul_eq ?_).mpr h
    norm_num

  -- simplify right-hand side
  rw [h1]
  ring


example (z : ℂ) : 5*z = I ↔ z = (1/5)*I := by
  constructor
  · -- the forward direction
    intro h
    rw [mul_comm 5 z] at h
    -- isolate z
    have h1 : z = I/5 := by
      apply (eq_div_iff_mul_eq ?_).mpr h
      norm_num
    -- simplify right-hand side
    rw [h1]
    ring
  · -- the backward direction
    intro h
    rw [h]
    ring

example (z : ℂ) : I*z = 2 →  z = -2*I := by
  intro h
  rw [mul_comm I z] at h

  have hnz : I ≠ 0 := by
    apply_fun im; norm_num

  -- isolate z
  have h1 : z = 2/I := by
    apply (eq_div_iff_mul_eq hnz).mpr h

  -- simplify right-hand side
  rw [h1]
  field_simp [hnz]
  rw [I_sq]
  ring

-- Fuchs 10.2.12
-- solve 2*z + 2*I*z - 3 = 5*I
example (z : ℂ) : (2*z + 2*I*z - 3 = 5*I) →  z = 2 + (1/2)*I := by
  intro h

  -- bring -3 to the right-hand side
  have h1 : 2*z + 2 *I*z = 3 + 5 * I := by
    apply Eq.symm (add_eq_of_eq_sub' (Eq.symm h))

  -- factor out z
  have h2 : z * (2 + 2 * I)  = 3 + 5 * I := by
    simpa [left_distrib, mul_comm] using h1

  -- verify that 2+2*I is nonzero
  have hnz1 : 2+2*I ≠ 0 := by
    apply_fun re; norm_num

  -- isolate z
  have h_iso : z = (3 + 5 * I) / (2 + 2 * I) := by
    exact (eq_div_iff_mul_eq hnz1).mpr h2

  -- verify that 1+I is nonzero
  have hnz2 : 1+I ≠ 0 := by
    apply_fun im ; norm_num

  -- Simplify the right-hand side to 2 + (1/2)*I
  rw [h_iso]
  field_simp [hnz2]
  -- we now prove 3 + 5 * I = (1 + I) * (2 ^ 2 + I) by ring
  ring_nf
  rewrite [I_sq]
  ring

end linear_equation


section Complex_numbers_has_no_ordering

#check LinearOrder
#check IsStrictOrderedRing

-- Prove that the complex numbers cannot be given a linear order
-- that is compatible with its field structure.
-- If we assume ℂ has a linear order `≤` that satisfies the axiom of
-- a strict ordered ring, we can derive a contradiction.
--
-- A linear order is a total order: for any a,b, either a ≤ b or b ≤ a.
-- A strict ordered ring satisfies:
--   if a < b, then a + c < b + c for any c,
--   if a < b and c > 0, then a * c < b * c.
theorem not_linearOrderedField_complex
  (h1: LinearOrder ℂ) (h2: IsStrictOrderedRing ℂ)
    :  False := by

  -- In a linear ordered ring, every square is ≥ 0.
  have h0_le_I_sq : (0 : ℂ) ≤ I * I := by
    -- `mul_self_nonneg` says `0 ≤ x * x` in any linear ordered ring.
    simpa using (mul_self_nonneg I)

  -- But in ℂ we know `I * I = -1`.
  have h0_le_neg1 : (0 : ℂ) ≤ -1 := by
    simpa [I_mul_I] using h0_le_I_sq

  -- Add 1 to both sides: 0 + 1 ≤ -1 + 1, so 1 ≤ 0.
  have h1_le_0 : (1 : ℂ) ≤ 0 := by
    have := add_le_add_right h0_le_neg1 1
    -- Simplify both sides.
    simpa [add_comm, add_left_comm, add_assoc] using this

  -- In a linear ordered ring we must have 0 < 1.
  have h0_lt_1 : (0 : ℂ) < 1 := by norm_num

  -- Combining: 1 < 1, contradiction.
  have : (1 : ℂ) < 1 := by exact lt_of_le_of_lt h1_le_0 h0_lt_1
  exact lt_irrefl 1 this


end Complex_numbers_has_no_ordering


section Prop_1_3_2
/-
Proposition 1.3.2
		For complex numbers $z\in \mathbb{C}$:
			(1) $(z^*)^* = z$.
			(2)) $z^* = z$ if and only if $z$ is real.
			(3)) $z^* = -z$ if and only if $z$ is purely imaginary.
-/


open Complex

-- Define the usual notation for complex conjugate
notation "conj" => (starRingEnd ℂ)

/-
conj conj z = z
-/
lemma conj_conj (z : ℂ) : conj (conj z) = z := by
-- Use extensionality on real and imaginary parts
  apply Complex.ext
  · -- real parts are equal
    simp
  · -- imaginary parts are equal
    simp


/-
  conj z = z if and only if imag(z) = 0
-/
example (z : ℂ) : conj z = z ↔ z.im = 0 := by
  constructor
  · -- conj z = z → z.im = 0
    intro h
    -- Two complex numbers are equal iff their components are equal
    rw [Complex.ext_iff] at h
    -- Break h into real (h_re) and imaginary (h_im) parts
    obtain ⟨h_re, h_im⟩ := h
    -- Simplify (conj z).im to -z.im
    simp at h_im
    -- We now have -z.im = z.im. Arithmetic solves this.
    linarith
  · -- z.im = 0 → conj z = z
    intro h
    -- To prove two complex numbers are equal, check components
    -- and use the hypothesis that Im(z)=0
    simp [Complex.ext_iff, h]

/-
    z* = -z if and only if real(z) = 0
-/
example (z : ℂ) : conj z = -z ↔ z.re = 0 := by
  constructor
  · -- conj z = -z → z.re = 0
    intro h
    -- Two complex numbers are equal iff their components are equal
    rw [Complex.ext_iff] at h
    -- Break h into real (h_re) and imaginary (h_im) parts
    obtain ⟨h_re, h_im⟩ := h
    -- Simplify (conj z).re to -z.re
    simp at h_re
    -- We now have z.re = -z.re
    linarith
  · -- z.re = 0 → conj z = -z
    intro h
    -- To prove two complex numbers are equal, we check the components
    -- and use the hypothesis that real(z)=0
    simp [Complex.ext_iff, h]

end Prop_1_3_2
