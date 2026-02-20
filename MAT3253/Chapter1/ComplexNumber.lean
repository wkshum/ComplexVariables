/-

  Proofs of selected theorems in Chapter 1

-/

import Mathlib.Tactic

set_option linter.style.commandStart false
set_option linter.style.induction false

open Complex   -- open the Complex namespace


section Complex_number

-- Find the real and imaginary part of 3-5i
#eval Complex.re (3 - 5*I)
#eval Complex.im (3 - 5*I)

-- Find the real and imaginary part of 7
#eval Complex.re (7)
#eval Complex.im (7)


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


end Complex_number



section linear_equation

-- Solve 5z=i
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

-- i/5 is the only solution to 5z=i
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

-- solve iz = 2
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

-- Define the usual notation for complex conjugate
notation "conj" => (starRingEnd ℂ)


section prop_1_3_2
/-
Proposition 1.3.2
		For complex numbers $z\in \mathbb{C}$:
			(1) $(z^*)^* = z$.
			(2)) $z^* = z$ if and only if $z$ is real.
			(3)) $z^* = -z$ if and only if $z$ is purely imaginary.
-/


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

end prop_1_3_2



section Theorem_1_3_3
-- Define the usual notation for complex conjugate
-- notation "conj" => (starRingEnd ℂ)


/-
Theorem 1.3.3
  (z_1 + z_2)^* = z_1^* + z_2^* and (z_1 z_2)^* = z_1^* z_2^*
-/

theorem conj_add_conj (z₁ z₂ : ℂ) : conj z₁ + conj z₂ = conj (z₁ + z₂) := by
  -- define a, b, c, d 
  let a := z₁.re; let b := z₁.im
  let c := z₂.re; let d := z₂.im
  
  calc
    -- Expand z₁ and z₂ into components: (a + bi)^* + (c + di)^*
    conj z₁ + conj z₂ 
    -- Apply conjugate definition: (a - bi) + (c - di)
    _ = Complex.mk a (-b) + Complex.mk c (-d) := by rfl
    -- Group real and imaginary parts: (a + c) - i(b + d)
    _ = Complex.mk (a + c) (-(b + d)) := by
       ring_nf
       rfl
    -- By definition, it equals conj (z₁+z₂)
    _ = conj (z₁ + z₂) := by rfl


theorem conj_mul_conj (z₁ z₂ : ℂ) : conj z₁ * conj z₂ = conj (z₁ * z₂) := by
  -- define a,b,c,d
  let a := z₁.re; let b := z₁.im
  let c := z₂.re; let d := z₂.im
  
  calc
    -- Expand z₁ and z₂
    conj z₁ * conj z₂ 
    -- Apply conjugate definition
    _ = Complex.mk a (-b) * Complex.mk c (-d) := by rfl
    -- Perform complex multiplication
    -- We want to reach (ac - bd) - i(ad + bc)
    -- Use Extensionality to split into Real and Imaginary goals
    _ = Complex.mk (a * c - b * d) (-(a * d + b * c)) := by 
         apply Complex.ext 
         · simp
         · simp
           ring 
    -- The rest is true by definition
    _ = conj (z₁ * z₂)  := by rfl


/-
   conj z⁻¹ = (conj z)⁻¹
-/
example (z : ℂ) (hz : z ≠ 0) : conj z⁻¹ = (conj z)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
    
  -- Now we perform the calculation: z*(1/z) = ... = 1
  calc
    conj z * conj z⁻¹  
    -- Combine conjugates: (1/z)* z* = ((1/z)z)*
    -- Note: map_mul is (x*y)* = x* * y*, so we use ← to go backwards
    _ = conj (z*z⁻¹) := by rw [← map_mul]
    
    -- Simplify z(1/z) to 1
    _ = conj 1         := by rw [Complex.mul_inv_cancel hz]

    -- Conjugate of 1 is 1
    _ = 1         := by rw [map_one]


-- Prove by applying existing theorems in Mathlib
example (z₁ z₂ : ℂ) : conj z₁ + conj z₂ = conj (z₁ + z₂) := by
  exact Eq.symm (RingHom.map_add (starRingEnd ℂ) z₁ z₂)

example (z₁ z₂ : ℂ) : conj z₁ * conj z₂ = conj (z₁ * z₂) := by 
  exact Eq.symm (RingHom.map_mul (starRingEnd ℂ) z₁ z₂)

example (z : ℂ) : conj z⁻¹ = (conj z)⁻¹ := by
  exact Complex.conj_inv z

end Theorem_1_3_3




section Theorem_1_3_4
/-
Theorem 1.3.4, Part (i), z z^* = a^2 + b^2
-/

-- detailed proof
example (z : ℂ) :
    z * conj z = (z.re)^2 + (z.im)^2 := by
  let a := z.re; let b := z.im
  
  calc
    z * conj z 
    -- Apply conjugate: (a + bi)(a - bi)
    _ = (Complex.mk a b) * (Complex.mk a (-b))   := by rfl
    
    -- Definition of multiplication: (aa - b(-b)) + i(a(-b) + ba)
    _ = Complex.mk (a * a - b * (-b)) (a * (-b) + b * a) := by rfl
    
    -- Simplify Algebra: a^2 + b^2 + i(0)
    _ = Complex.mk (a ^ 2 + b ^ 2) 0  := by 
      congr
      · ring -- Real part: a*a - (-b^2) = a^2 + b^2
      · ring -- Imaginary part: -ab + ab = 0

    -- Convert Complex.mk x 0 to just real number x (casted to Complex)
    _ = (a ^ 2 + b ^ 2 : ℂ)   :=  by
        apply Complex.ext
        · simp 
          rw [← Complex.ofReal_pow a 2, ← Complex.ofReal_pow b 2]
          repeat rw [Complex.ofReal_re] 
        · simp 
          rw [← Complex.ofReal_pow a 2, ← Complex.ofReal_pow b 2]
          repeat rw [ofReal_im]
          ring

-- proof using `mul_conj`
example (z : ℂ) :
    z * conj z = (z.re)^2 + (z.im)^2 := by
  rw [Complex.mul_conj]
  unfold normSq
  simp
  ring


/-
Theorem 1.3.4, Part (iia) z.re = (z + conj z) / 2 
-/

example (z : ℂ) : z.re = (z + conj z) / 2  := by 
  let a := z.re
  let b := z.im
  
  symm
  calc
    (z + conj z) / 2 
    -- Expand z to Complex.mk a b
    _ = (Complex.mk a b + conj (Complex.mk a b)) / 2 := by rfl
    
    -- Apply definition of conjugate
    _ = (Complex.mk a b + Complex.mk a (-b)) / 2     := by rfl
    
    -- Perform the addition: (a+a) + i(b-b)
    _ = (Complex.mk (a + a) (b + -b)) / 2             := by rfl
    
    -- Simplify the numerator: 2a + i0
    _ = (Complex.mk (2 * a) 0) / 2   := by 
      congr 2 -- Focus inside the 'mk'
      · ring -- Real part: a + a = 2 * a
      · ring -- Imaginary part: b + -b = 0
      
    -- Convert 'mk (2a) 0' to the casted real number '(2a : ℂ)'
    _ = (2 * a : ℂ) / 2    := by 
        apply Complex.ext
        · simp
        · simp
    _ = a := by simp

-- prove by considering real and imaginary parts at the beginning      
example (z : ℂ) : z.re = (z + conj z) / 2 := by
  apply Complex.ext

  -- Goal 1: Real parts match
  -- LHS: z.re
  -- RHS: ((z + conj z) / 2).re
  · simp

  -- Goal 2: Imaginary parts match
  -- LHS: 0 (since z.re is real)
  -- RHS: ((z + conj z) / 2).im
  · simp


/-
Theorem 1.3.4, Part (iib) z.im = (z - conj z) / (2i) 
-/
example (z : ℂ) : z.im = (z - conj z) / (2*I)  := by 
  symm
  -- Multiply both sides by 2*I to avoid fraction headaches
  rw [div_eq_iff]
  -- Use Extensionality to check Real/Imaginary parts
  · apply Complex.ext
    · simp -- Real parts match (0 = 0)
    · simp
      ring
       -- Imaginary parts match (2b = 2b)

  -- Prove denominator non-zero
  · simp [I_ne_zero]

-- prove using and existing theorem in Mathlib
example (z : ℂ) : z.re = (z + conj z) / 2  := by
  exact re_eq_add_conj z

-- prove using and existing theorem in Mathlib
example (z : ℂ) : z.im = (z - conj z) / (2*I)  := by
  exact im_eq_sub_conj z

end Theorem_1_3_4



section Theorem_1_3_6
/-
  Theorem 1.3.6, part (i), z z^* = |z|^2
-/
example (z : ℂ) : z * conj z = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj]  -- z (conj z) = normSq z
  rw [← Complex.ofReal_pow]
  norm_cast
  exact normSq_eq_norm_sq z -- reduce to show:  normSq z = ‖z‖ ^ 2


/-
Theorem 1.3.6, part (ii)
|z₁ z₂| = |z₁| |z₂|
-/  
-- detailed proof
example (z₁ z₂ : ℂ) : ‖z₁ * z₂‖  = ‖z₁‖ * ‖z₂‖ := by
  -- Since norms are non-negative, x = |x|. 
  -- We rewrite the goal A = B to |A| = |B| so the lemma matches.
  rw [← abs_of_nonneg (norm_nonneg _)]
  rw [← abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

  -- Apply the API: |A| = |B| ↔ A^2 = B^2
  rw [← sq_eq_sq_iff_abs_eq_abs]

  -- "To prove real x = y, it suffices to prove complex ↑x = ↑y"
  rw [← ofReal_inj] 

  -- Switch to Complex numbers to use conjugate properties
  push_cast

  -- Finish the proof by calculations
  calc
    (‖z₁ * z₂‖ : ℂ) ^ 2 
    _ = (z₁ * z₂) * conj (z₁ * z₂)      := by rw [← mul_conj' (z₁*z₂)]
    _ = (z₁ * z₂) * (conj z₁ * conj z₂) := by rw [map_mul]
    _ = (z₁ * conj z₁) * (z₂ * conj z₂) := by ring
    _ = (‖z₁‖ : ℂ)^2 * (‖z₂‖ : ℂ)^2     := by rw [mul_conj' z₁ , mul_conj' z₂]
    _ = (‖z₁‖ * ‖z₂‖ : ℂ) ^ 2           := by rw [mul_pow]; 

-- prove by using existing api in Mathlib
example (z₁ z₂ : ℂ) : ‖z₁ * z₂‖  = ‖z₁‖ * ‖z₂‖ := by exact Complex.norm_mul z₁ z₂


end Theorem_1_3_6


section Theorem_1_3_7
/-
 Theorem 1.3.7, Triangle inequality |z₁+z₂| ≤ |z₁| + |z₂|
-/

-- use existing theorems in Mathlib
example (z₁ z₂ : ℂ) : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := by exact norm_add_le z₁ z₂

-- detailed proof
example (z₁ z₂ : ℂ) : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := by
  -- Since norms are non-negative, x = |x|. 
  -- We rewrite the goal A = B to |A| = |B| so the lemma matches.
  rw [← abs_of_nonneg (norm_nonneg _)]
  rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]

  -- Apply the API: |A| = |B| ↔ A^2 = B^2
  rw [←sq_le_sq]
  
  have h : ‖z₁ + z₂‖ ^ 2 = ‖z₁‖^2 + ‖z₂‖^2 + 2 * (z₁ * conj z₂).re := by 
    -- Convert Norm^2 to Real Part of (z * conj z)
    rw [← normSq_eq_norm_sq]
    rw [← ofReal_re (normSq (z₁ + z₂))]
    rw [← mul_conj]
    rw [RingHom.map_add]
    ring_nf  -- Expand the algebraic product: z1z1* + z1z2* + z2z1* + z2z2*
    -- Distribute `re` across the addition
    rw [add_re]
    -- Convert (z * conj z).re back to ‖z‖^2
    -- We do this for z1 and z2.
    -- The sequence is: (z * conj z).re -> (normSq z).re -> normSq z -> ‖z‖^2
    simp only [mul_conj, ofReal_re, normSq_eq_norm_sq]
    rw [add_re, add_re]
    -- Key step: z2 * z1* is the conjugate of z1 * z2*
    -- And a complex number and its conjugate have the same Real part.
    simp only [ofReal_re]
    -- Simplify the conjugate term: conj(z2 * conj z1) -> z1 * conj z2
    rw [← conj_re (z₂ * conj z₁)] 
    -- Simplify Re(↑‖z1‖^2) to ‖z1‖^2
    rw [map_mul, conj_conj, mul_comm]
    -- the rest is algebra
    ring

  calc
    ‖z₁ + z₂‖ ^ 2 
    _ = ‖z₁‖^2 + ‖z₂‖^2 + 2 * (z₁ * conj z₂).re := by rw [h]
    -- Apply Inequality: Re(w) <= |w| 
    _ ≤ ‖z₁‖^2 + ‖z₂‖^2 + 2 * ‖z₁ * conj z₂‖ := by 
        gcongr -- 1. Strips away the common terms (squares and the factor 2)
        apply re_le_norm -- 2. Applies Re(w) ≤ ‖w‖
    -- Break product |z1 z2*| = |z1| |z2|
    _ = ‖z₁‖^2 + ‖z₂‖^2 + 2 * (‖z₁‖ * ‖conj z₂‖) := by rw [norm_mul]
    _ = ‖z₁‖^2 + ‖z₂‖^2 + 2 * ‖z₁‖ * (‖conj z₂‖) := by ring
    _ = ‖z₁‖^2 + ‖z₂‖^2 + 2 * ‖z₁‖ * (‖z₂‖) := by rw [norm_conj]
    -- Factor perfect square
    _ = (‖z₁‖ + ‖z₂‖) ^ 2 := by ring


end Theorem_1_3_7


section Theorem_1_4_4

/-
Theorem 1.4.4 DeMoivre formula
For integer n,
(cos θ + i* sin θ)^n = cos (nθ) + i * sin (nθ)
-/


/-
We first prove DeMoivre formula for nonnegative integers
-/

-- Prove 1: Prove by induction
theorem DeMoivre (θ : ℝ) (n : ℕ) :
(cos θ + sin θ * I) ^ n = cos (n * θ) + sin (n * θ) * I := by
-- 1. Start Induction on n
induction n with
|   zero =>
-- Base case: n = 0
-- LHS = (...)^0 = 1
-- RHS = cos 0 + sin 0 * I = 1 + 0 = 1
simp
|   succ n ih =>
-- Inductive step: Assume true for n, prove for n + 1
-- Rewrite z^(n+1) as z^n * z
-- Apply the induction hypothesis
rw [pow_succ, ih] 

-- Handle the arguments inside cos and sin: (n + 1) * θ = n * θ + θ
simp only [Nat.cast_succ, add_mul, one_mul]

--Use Complex.ext to check Real and Imaginary parts separately
apply Complex.ext
· simp [cos_add, sin_add]
  ring
· simp [sin_add, cos_add]
  ring

-- Proof 2: Prove by the tactic `induction'`
theorem DeMoivre' (θ : ℝ) (n : ℕ) :
(cos θ + sin θ * I) ^ n = cos (n * θ) + sin (n * θ) * I := by
induction' n with m induction_hypothesis
· -- base case
  simp
· -- induction step
  rw [pow_succ, induction_hypothesis] 
  simp only [Nat.cast_succ, add_mul, one_mul]
  apply Complex.ext
  · simp [cos_add, sin_add]
    ring
  · simp [sin_add, cos_add]
    ring

-- Proof 3: Prove using Euler's formula
-- This is an existing theorem in Mathlib
theorem DeMoivre'' (θ : ℝ) (n : ℕ) :
(cos θ +  sin θ * I)^n = (cos (n*θ) +  (sin (n*θ)) * I) := by
exact cos_add_sin_mul_I_pow n θ

/-
Next, prove the DeMoivre formula for negative exponent.
We need two helper lemmas
-/

/- Helper lemma 1
the inverse of e^(x*I) is equal to exp(-x*I)
-/
lemma one_dvd_mul_I (x : ℝ) : 1/(exp (x*I)) = exp (- (x*I)) := by
have h: exp (x*I) ≠ 0 := by exact exp_ne_zero (x*I)
field_simp [h]
symm
-- Want to show exp (x * I) * exp (-(x * I)) = 1
calc
(x * I).exp* (-(x * I)).exp 
= ((x * I) + (-(x * I)) ).exp := by rw [← exp_add (x*I) (-(x*I))]
_ = exp (0) := by rw [add_neg_cancel]
_ = 1 := by rw [exp_zero]

/- Helper lemma 2
the inverse of (cos (x) + sin (x) *I) equals cos (-x) + sin (-x) *I
-/
lemma DeMoivre_helper (x : ℝ) : 
1/(cos (x) + sin (x) *I) = cos (-x) + sin (-x) *I := by
rw [← exp_mul_I x]
rw [one_dvd_mul_I]
rw [← exp_mul_I (-x)]
apply congr_arg exp ?_
ring


-- DeMoivre formula for negative integer exponent
theorem DeMoivre_neg_exp (x : ℝ) (n : ℕ) :
1/(cos (x) + sin (x) *I)^n = cos (-n*x) + (sin (-n*x)) * I := by

have hD : 1/(cos (x) + sin (x) *I)^n = cos (n*(-x)) +  sin (n*(-x)) * I := by
  rw [← one_div_pow (cos (x) + sin (x) *I) n]
  rw [DeMoivre_helper]
  exact cos_add_sin_mul_I_pow n (-x)

calc
1/(cos (x) + sin (x) *I)^n = cos (n*(-x)) +  sin (n*(-x)) * I := by rw [hD]
_ = cos (-n*x) +  sin (-n*x) * I := by ring_nf

/-
DeMoivre formula for all integers
-/
theorem DeMoivre_formula (θ : ℝ) (n : ℤ) :
(cos θ +  sin θ * I)^n = (cos (n*θ) +  (sin (n*θ)) * I) := by
cases n with
| ofNat m =>
-- Case 1: n is a non-negative integer (n = 0, 1, 2...)
-- We convert the Integer n back to Natural number m
simp
-- Apply the first theorem for nonnegative integers
exact DeMoivre θ m

| negSucc m =>
-- Case 2: n is a negative integer (n = -1, -2...)
-- negSucc m is technically -(m + 1)

-- 1. Convert integer syntax to real number arithmetic:
--    LHS: z ^ -(m+1) becomes 1 / z^(m+1)
--    RHS: n * θ becomes -(m+1) * θ
simp only [Int.negSucc_eq, zpow_neg, Int.cast_neg]

-- 2. Now the goal matches `DeMoivre_neg_exp`` perfectly
--    Goal: 1 / (...) ^ (m+1) = cos (-(m+1)*θ) ...
rw [inv_eq_one_div]
exact DeMoivre_neg_exp θ (m + 1)

end Theorem_1_4_4
