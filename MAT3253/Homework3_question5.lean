/-
  MAT3253 Complex variables
  Homework 3 Question 5
-/


import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic

open Complex

variable {a b c d : ℂ}

/-- Möbius map `T(z) = (a z + b) / (c z + d)` -/
noncomputable def T (z : ℂ) : ℂ := (a * z + b) / (c * z + d)

/--
“`f(z) → ∞` as `z → ∞`” in an elementary form:

For every real `M`, there exists `R` such that if `‖z‖ ≥ R` then `‖f z‖ ≥ M`.
-/


def TendstoInfinity (f : ℂ → ℂ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → M ≤ ‖f z‖

/-!
  ### Part (a)
If `c = 0` and `ad - bc ≠ 0`, then `T(z) → ∞` as `z → ∞`
(in the elementary “for every `M` exists `R` ...” sense).

Idea (as in a complex analysis course):
* if `c = 0` then `T(z) = (a/d) z + (b/d)` is affine;
* since `ad ≠ 0`, we have `a ≠ 0` and `d ≠ 0`, so the slope `a/d` is nonzero;
* hence `‖(a/d) z + (b/d)‖` grows at least like `‖a/d‖‖z‖ - ‖b/d‖`.
-/
theorem mobius_tendsToInfinity_of_c_eq_zero
    (hdet : a * d - b * c ≠ 0) (hc : c = 0) :
    TendstoInfinity (T (a := a) (b := b) (c := c) (d := d)) := by
  --------------------------------------------------------------------
  -- Step 1: from `ad - bc ≠ 0` and `c=0`, deduce `a ≠ 0` and `d ≠ 0`.
  --------------------------------------------------------------------
  have had : a * d ≠ 0 := by simpa [hc] using hdet
  have ha : a ≠ 0 := (mul_ne_zero_iff.mp had).1
  have hd : d ≠ 0 := (mul_ne_zero_iff.mp had).2

  --------------------------------------------------------------------
  -- Step 2: if `c=0` then `T(z)` becomes an affine map `α*z + β`.
  --------------------------------------------------------------------
  let α : ℂ := a / d
  let β : ℂ := b / d

  have hT : ∀ z : ℂ, T (a := a) (b := b) (c := c) (d := d) z = α * z + β := by
    intro z
    -- Replace `c` by `0` and simplify.
    calc
      T (a := a) (b := b) (c := c) (d := d) z
          = (a * z + b) / (c * z + d) := by rfl
      _ = (a * z + b) / d := by simp [hc, add_comm]
      _ = (a * z) / d + b / d := by simp [add_div]
      _ = (a / d) * z + b / d := by simp [div_mul_eq_mul_div]
      _ = α * z + β := by simp [α, β]

  -- `α ≠ 0`, hence `‖α‖ > 0`.
  have hα : α ≠ 0 := div_ne_zero ha hd
  have hαpos : 0 < ‖α‖ := by simpa [norm_pos_iff] using hα
  have hαne : (‖α‖ : ℝ) ≠ 0 := ne_of_gt hαpos

  --------------------------------------------------------------------
  -- Step 3: prove the “∀M ∃R …” condition.
  --------------------------------------------------------------------
  intro M
  refine ⟨(M + ‖β‖) / ‖α‖, ?_⟩
  intro z hz

  --------------------------------------------------------------------
  -- Step 4: a standard inequality:
  --   ‖α*z + β‖ ≥ ‖α*z‖ - ‖β‖ = ‖α‖‖z‖ - ‖β‖.
  --
  -- We use `norm_sub_norm_le` with `x = α*z` and `y = -β`:
  --   ‖x‖ - ‖y‖ ≤ ‖x - y‖.
  --------------------------------------------------------------------
  have hlow : ‖α‖ * ‖z‖ - ‖β‖ ≤ ‖α * z + β‖ := by
    calc
      ‖α‖ * ‖z‖ - ‖β‖ = ‖α * z‖ - ‖β‖ := by simp 
      _ = ‖α * z‖ - ‖-β‖ := by simp [norm_neg]
      _ ≤ ‖α * z - (-β)‖ := by simpa using (norm_sub_norm_le (α * z) (-β))
      _ = ‖α * z + β‖ := by simp [sub_eq_add_neg, add_comm]

  --------------------------------------------------------------------
  -- Step 5: from `hz : (M+‖β‖)/‖α‖ ≤ ‖z‖` get `M ≤ ‖α‖‖z‖ - ‖β‖`.
  --------------------------------------------------------------------
  have hstep1 :
      ‖α‖ * ((M + ‖β‖) / ‖α‖) ≤ ‖α‖ * ‖z‖ :=
    mul_le_mul_of_nonneg_left hz (le_of_lt hαpos)

  have hstep1' : M + ‖β‖ ≤ ‖α‖ * ‖z‖ := by
    -- Start from `hstep1 : ‖α‖ * ((M+‖β‖)/‖α‖) ≤ ‖α‖ * ‖z‖`
    -- and simplify the left side using `‖α‖ ≠ 0`.
    have hcancel : ‖α‖ * (M + ‖β‖) / ‖α‖ = (M + ‖β‖) := by 
      simpa using (mul_div_cancel_left₀ (M + ‖β‖) hαne)
    have hrew :
      ‖α‖ * (M + ‖β‖) / ‖α‖ = ‖α‖ * ((M + ‖β‖) / ‖α‖) := by
        simpa using (mul_div_assoc ‖α‖ (M + ‖β‖) ‖α‖)
    -- rewrite the left-hand side of `h` using `hcancel`
    rw [← hrew] at hstep1
    simpa [hcancel] using hstep1

  have hstep2 : M ≤ ‖α‖ * ‖z‖ - ‖β‖ := by
    -- subtract `‖β‖` from both sides of `hstep1'`
    have := sub_le_sub_right hstep1' ‖β‖
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

  --------------------------------------------------------------------
  -- Step 6: combine the inequalities and rewrite back to `T`.
  --------------------------------------------------------------------
  have : M ≤ ‖α * z + β‖ := le_trans hstep2 hlow
  simpa [hT z] using this





/-!   ### Part (b1)
Elementary (epsilon–`R`) definition of “`f(z) → w` as `z → ∞`”:

For every `ε > 0` there exists `R` such that for all `z` with `‖z‖ ≥ R`,
we have `‖f z - w‖ < ε`.
-/
def TendstoAtInfinity (f : ℂ → ℂ) (w : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖f z - w‖ < ε

/-!  
Prove that, if `c ≠ 0`, then  we have
`T(z) → a/c` as `z → ∞` (epsilon–`R` sense).

Idea:
`T(z) - a/c = (b*c - a*d) / (c*(c*z + d))`, so its norm is bounded by a constant times `1/‖z‖`.
-/

theorem mobius_tendstoAtInfinity_a_div_c (hc : c ≠ 0) :
    TendstoAtInfinity (T (a := a) (b := b) (c := c) (d := d)) (a / c) := by
  intro ε hε

  -- Basic positivity facts
  have hcpos : 0 < ‖c‖ := by simpa [norm_pos_iff] using hc
  have hcne : (‖c‖ : ℝ) ≠ 0 := ne_of_gt hcpos

  -- Constants used to choose a “large enough” radius `R`.
  -- `R₁` guarantees `‖c*z + d‖` is comparable to `‖c‖‖z‖` for large `z`.
  -- `K` is a convenient constant depending only on `a b c d`.
  let R₁ : ℝ := (2 * ‖d‖) / ‖c‖
  let K  : ℝ := (2 * ‖b * c - a * d‖) / (‖c‖ ^ 2)
  -- `R₂` is chosen so that `K / ‖z‖ < ε` once `‖z‖ ≥ R₂`.
  let R₂ : ℝ := K / ε + 1
  -- Final radius: big enough for both purposes (and also ≥ 1).
  let R : ℝ := 1 + R₁ + R₂

  refine ⟨R, ?_⟩
  intro z hz

  --------------------------------------------------------------------
  -- Step 1: show `‖c*z + d‖` is bounded below by `(‖c‖*‖z‖)/2`
  --         once `‖z‖ ≥ R₁`.
  --------------------------------------------------------------------

  have hR₁_le : R₁ ≤ ‖z‖ := by
    have : R₁ ≤ R := by
      -- `R = 1 + R₁ + R₂` so this is clear once `0 ≤ 1 + R₂`.
      have : 0 ≤ (1 : ℝ) + R₂ := by
        -- `R₂ = K/ε + 1` so it is ≥ 1.
        dsimp [R₂]
        -- K is a norm squared stuff, so non-negative. ε > 0.
        have hK_nonneg : 0 ≤ K := by
          dsimp [K]
          exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (pow_two_nonneg _)
        -- 2. Show K/ε ≥ 0
        have h_ratio_nonneg : 0 ≤ K / ε := div_nonneg hK_nonneg (le_of_lt hε)
        -- 3. Conclude 1 + (K/ε + 1) ≥ 0
        linarith

      -- Now conclude by linear arithmetic.
      dsimp [R]; nlinarith
    exact le_trans this hz

  -- Multiply `R₁ ≤ ‖z‖` by `‖c‖ > 0` to get `2‖d‖ ≤ ‖c‖‖z‖`.
  have h2d_le : (2 * ‖d‖) ≤ ‖c‖ * ‖z‖ := by
    have h := mul_le_mul_of_nonneg_left hR₁_le (le_of_lt hcpos)
    -- simplify the left side: `‖c‖ * ((2‖d‖)/‖c‖) = 2‖d‖`
    unfold R₁ at h
    rw [← mul_div_assoc] at h
    rw [mul_div_cancel_left₀ _ hcne] at h
    exact h

  -- Hence `‖d‖ ≤ (‖c‖‖z‖)/2`.
  have hd_le_half : ‖d‖ ≤ (‖c‖ * ‖z‖) / 2 := by nlinarith [h2d_le]

  -- Triangle inequality in a useful rearranged form:
  -- `‖c*z + d‖ ≥ ‖c*z‖ - ‖d‖ = ‖c‖‖z‖ - ‖d‖`.
  have htri : ‖c‖ * ‖z‖ - ‖d‖ ≤ ‖c * z + d‖ := by
    -- `norm_sub_norm_le (c*z) (-d)` gives: `‖c*z‖ - ‖-d‖ ≤ ‖c*z - (-d)‖`
    simpa [norm_mul, norm_neg, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (norm_sub_norm_le (c * z) (-d))

  -- Combine: `(‖c‖‖z‖)/2 ≤ ‖c‖‖z‖ - ‖d‖ ≤ ‖c*z + d‖`.
  have hden_lower : (‖c‖ * ‖z‖) / 2 ≤ ‖c * z + d‖ := by
    have : (‖c‖ * ‖z‖) / 2 ≤ ‖c‖ * ‖z‖ - ‖d‖ := by nlinarith [hd_le_half]
    exact le_trans this htri

  -- In particular `c*z + d ≠ 0` (since its norm is > 0).
  have hzpos : 0 < ‖z‖ := by
    -- From `R ≤ ‖z‖` and `R ≥ 1` we get `‖z‖ ≥ 1`.
    have hRge1 : (1 : ℝ) ≤ R := by
      -- because `R = 1 + R₁ + R₂` and `R₁,R₂ ≥ 0`
      -- we only need `0 ≤ R₁` and `0 ≤ R₂`, both are true.
      have hR₁nonneg : 0 ≤ R₁ := by
        dsimp [R₁]
        exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg d)) (le_of_lt hcpos)
      have hR₂nonneg : 0 ≤ R₂ := by 
        dsimp [R₂]
        -- 1. Show K ≥ 0
        have hK_nonneg : 0 ≤ K := by
          dsimp [K]
          exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (pow_two_nonneg _)
        -- 2. Show K/ε ≥ 0
        have h_ratio_nonneg : 0 ≤ K / ε := div_nonneg hK_nonneg (le_of_lt hε)
        -- 3. Conclude 0 ≤ K/ε + 1
        linarith
      dsimp [R]; nlinarith
    have : (1 : ℝ) ≤ ‖z‖ := le_trans hRge1 hz
    exact lt_of_lt_of_le (by norm_num) this

  have hczd_ne : c * z + d ≠ 0 := by
    have : 0 < ‖c * z + d‖ := by
      -- `(‖c‖‖z‖)/2 > 0` and it is ≤ `‖c*z + d‖`
      have : 0 < (‖c‖ * ‖z‖) / 2 :=
        div_pos (mul_pos hcpos hzpos) (by norm_num)
      exact lt_of_lt_of_le this hden_lower
    exact (norm_pos_iff).1 this

  --------------------------------------------------------------------
  -- Step 2: compute `T(z) - a/c` and bound its norm.
  --------------------------------------------------------------------

  -- Algebraic identity for the difference (valid once `c*z + d ≠ 0`).
  have hdiff :
      T (a := a) (b := b) (c := c) (d := d) z - a / c
        = (b * c - a * d) / (c * (c * z + d)) := by
    have hzcd_ne : z * c + d ≠ 0 := by 
      -- follows from `c*z + d ≠ 0` by commutativity of multiplication
      rw [mul_comm c z] at hczd_ne
      exact hczd_ne
    unfold T
    field_simp [hc,hczd_ne, hzcd_ne]
    ring
    

  -- Turn that identity into a norm estimate.
  have hnorm :
      ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖
        = ‖b * c - a * d‖ / (‖c‖ * ‖c * z + d‖) := by
    simp [hdiff]

  -- Use `‖c*z + d‖ ≥ (‖c‖‖z‖)/2` to get a `1/‖z‖` bound.
  have hbound : ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖ ≤ K / ‖z‖ := by
    -- First rewrite using `hnorm`.
    rw [hnorm]

    -- From `hden_lower`, multiply by `‖c‖ ≥ 0`.
    have hden2 :
        (‖c‖ * ((‖c‖ * ‖z‖) / 2)) ≤ (‖c‖ * ‖c * z + d‖) := by
      exact mul_le_mul_of_nonneg_left hden_lower (norm_nonneg c)

    -- Now divide by the (larger) denominator to make the fraction smaller.
    have hfrac :
        ‖b * c - a * d‖ / (‖c‖ * ‖c * z + d‖)
          ≤ ‖b * c - a * d‖ / (‖c‖ * ((‖c‖ * ‖z‖) / 2)) := by
      -- 1. Prove the smaller denominator is strictly positive
      have h_denom_pos : 0 < ‖c‖ * ((‖c‖ * ‖z‖) / 2) := by
        apply mul_pos hcpos
        apply div_pos
        · exact mul_pos hcpos hzpos
        · norm_num -- proves 0 < 2

      -- 2. Apply the monotonicity lemma
      exact div_le_div_of_nonneg_left (norm_nonneg _) h_denom_pos hden2

    -- Finally simplify the right-hand side to `K / ‖z‖`.
    -- (This is just algebra in `ℝ`.)
    have : ‖b * c - a * d‖ / (‖c‖ * ((‖c‖ * ‖z‖) / 2)) = K / ‖z‖ := by
      dsimp [K]
      -- `mul_div_assoc` is the rewrite `(x*y)/z = x*(y/z)`; then `ring`-style simp.
      -- We keep it mostly `simp`-based for readability.
      field_simp [hcne, hzpos.ne']
      

    exact le_trans hfrac (by simp [this])

  --------------------------------------------------------------------
  -- Step 3: choose `R₂` so that `K / ‖z‖ < ε`.
  --------------------------------------------------------------------

  have hR₂_le : R₂ ≤ ‖z‖ := by
    have : R₂ ≤ R := by
      -- since `R = 1 + R₁ + R₂` and `0 ≤ 1 + R₁`
      have : 0 ≤ (1 : ℝ) + R₁ := by
        have hR₁nonneg : 0 ≤ R₁ := by
          dsimp [R₁]
          exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg d)) (le_of_lt hcpos)
        nlinarith
      dsimp [R]; nlinarith
    exact le_trans this hz

  have hK_div_lt : K / ‖z‖ < ε := by
    -- From `R₂ ≤ ‖z‖` and `R₂ = K/ε + 1`, we get `K/ε < ‖z‖`.
    have hKε_lt : K / ε < ‖z‖ := by
      have : K / ε < R₂ := by
        dsimp [R₂]
        exact lt_add_of_pos_right _ (by norm_num)
      exact lt_of_lt_of_le this hR₂_le

    -- Multiply by `ε > 0`:
    have hmul : ε * (K / ε) < ε * ‖z‖ := mul_lt_mul_of_pos_left hKε_lt hε
    have hK_lt : K < ε * ‖z‖ := by
      rw [← mul_div_assoc ε K ε] at hmul
      rw [mul_div_cancel_left₀ K (ne_of_gt hε)] at hmul
      exact hmul

    rw [div_lt_iff₀ hzpos]
    assumption


  -- Final estimate:
  -- `‖T z - a/c‖ ≤ K/‖z‖ < ε`.
  exact lt_of_le_of_lt hbound hK_div_lt





/-!   ### Part (b2)
Definition of `f(z) → ∞` as `z → z₀`:
For every real `M`, there exists `δ > 0` such that if `0 < ‖z - z₀‖ < δ`, 
  then `M ≤ ‖f z‖`.
-/
def TendstoInfinityAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < δ → M ≤ ‖f z‖


theorem mobius_pole_limit
    (hc : c ≠ 0)
    (hdet : a * d - b * c ≠ 0) :
    TendstoInfinityAt (T (a := a) (b := b) (c := c) (d := d)) (-d / c) := by
  intro M

  -- 1. Setup constants and positivity
  let z₀ := -d / c
  have hcpos : 0 < ‖c‖ := by simpa [norm_pos_iff] using hc
  -- The numerator of the difference term: Δ = bc - ad
  let Δ := b * c - a * d
  have hΔ_ne : Δ ≠ 0 := by 
    dsimp [Δ]
    rw [← neg_sub (a * d) (b * c)]
    exact neg_ne_zero.mpr hdet

  have hΔpos : 0 < ‖Δ‖ := by simpa [norm_pos_iff] using hΔ_ne

  -- 2. Define the target magnitude for the singular part
  -- We want the singular part to be bigger than M + |a/c|.
  let Target := |M| + ‖a / c‖ + 1

  -- 3. Choose δ.
  -- We know |T(z) - a/c| = |Δ| / (|c|^2 * |z - z₀|).
  -- We want |Δ| / (|c|^2 * δ) = Target.
  -- So δ = |Δ| / (|c|^2 * Target).
  let δ := ‖Δ‖ / ((‖c‖ ^ 2) * Target)

  have hTarget_pos : 0 < Target := by
    dsimp [Target]
    have : 0 ≤ |M| + ‖a / c‖ := add_nonneg (abs_nonneg M) (norm_nonneg _)
    linarith

  have hδpos : 0 < δ := by
    dsimp [δ]
    apply div_pos hΔpos
    apply mul_pos (pow_two_pos_of_ne_zero (by simpa [norm_eq_zero] using hc)) hTarget_pos

  -- 4. Prove the limit condition
  refine ⟨δ, hδpos, ?_⟩
  intro z ⟨hz_pos, hz_lt⟩

  -- Useful Identity: c * z + d = c * (z - z₀)
  have h_denom : c * z + d = c * (z - z₀) := by
    dsimp [z₀]
    field_simp [hc]
    ring

  have h_denom_norm : ‖c * z + d‖ = ‖c‖ * ‖z - z₀‖ := by
    rw [h_denom, norm_mul]

  have h_denom_ne_zero : c * z + d ≠ 0 := by
    rw [h_denom]
    apply mul_ne_zero hc
    -- 0 < ‖w‖ ↔ w ≠ 0
    rw [← norm_pos_iff]
    exact hz_pos

  -- 5. Algebraic Separation: T(z) = a/c + Δ / (c(cz+d))
  have h_split : T (a := a) (b := b) (c := c) (d := d) z - a / c = Δ / (c * (c * z + d)) := by
    dsimp [T, Δ]
    have h_denom_ne_zero' : z * c + d ≠ 0 := by 
      rw [mul_comm c z] at h_denom_ne_zero
      exact h_denom_ne_zero
    field_simp [hc, h_denom_ne_zero, h_denom_ne_zero']
    ring

  -- 6. Lower bound using reverse triangle inequality
  -- |T(z)| ≥ |T(z) - a/c| - |a/c|
  have h_low : ‖T (a := a) (b := b) (c := c) (d := d) z‖
               ≥ ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖ - ‖a / c‖ := by
    have key := norm_sub_norm_le (T (a := a) (b := b) (c := c) (d := d) z - a / c) (-a / c)
    calc 
     ‖T (a := a) (b := b) (c := c) (d := d) z‖
               = ‖(T (a := a) (b := b) (c := c) (d := d) z - a / c) + (a / c)‖ := by
                      rw [sub_add_cancel]
             _ = ‖(T (a := a) (b := b) (c := c) (d := d) z - a / c) - (-a / c)‖ := by
                      rw [← sub_neg_eq_add]
                      ring_nf
             _ ≥ ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖ - ‖-a / c‖ := by
                    rel [key]
             _ = ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖ - ‖-(a / c)‖ := by
                    ring_nf
             _ = ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖ - ‖a / c‖ := by 
                    rw [norm_neg]
  
  -- Calculate the norm of the singular part
  have h_sing_val : ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖ 
      = ‖Δ‖ / (‖c‖^2 * ‖z - z₀‖) := by
    rw [h_split, norm_div, norm_mul, h_denom_norm]
    -- simplify denominator: ‖c‖ * (‖c‖ * ‖z-z₀‖) = ‖c‖^2 * ‖z-z₀‖
    ring_nf

  -- 7. Show the singular part is large enough
  have h_large : ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖ > Target := by
    rw [h_sing_val]
    -- Do NOT unfold z₀ here; it breaks the match with hz_pos.
    
    -- Helper: ‖c‖^2 > 0
    have h_c2_pos : 0 < ‖c‖ ^ 2 := pow_two_pos_of_ne_zero (by simpa using hc)

    -- 1. Apply lt_div_iff₀ to the goal
    -- Goal: Target < ‖Δ‖ / (‖c‖^2 * ‖z - z₀‖)
    -- We prove the denominator is positive using hz_pos (which uses z₀)
    rw [gt_iff_lt] 
    rw [lt_div_iff₀  (mul_pos h_c2_pos hz_pos)]
    
    -- 2. Apply lt_div_iff₀ to the hypothesis hz_lt
    -- Hypothesis: ‖z - z₀‖ < ‖Δ‖ / (‖c‖^2 * Target)
    rw [lt_div_iff₀ (mul_pos h_c2_pos hTarget_pos)] at hz_lt

    -- 3. Match the two sides
    -- Goal: Target * (‖c‖^2 * ‖z - z₀‖) < ‖Δ‖
    -- Hypothesis: ‖z - z₀‖ * (‖c‖^2 * Target) < ‖Δ‖
    convert hz_lt using 1
    ring


  -- 8. Final Combination
  -- |T(z)| ≥ Target - |a/c| = (|M| + |a/c| + 1) - |a/c| = |M| + 1 > M
  rw [ge_iff_le] at h_low
  apply le_of_lt
  calc
    M ≤ |M| := le_abs_self M
    _ < |M| + 1 := lt_add_of_pos_right _ (by norm_num)
    _ = Target - ‖a / c‖ := by dsimp [Target]; ring
    _ < ‖T (a := a) (b := b) (c := c) (d := d) z - a / c‖ - ‖a / c‖ := by
       apply sub_lt_sub_right h_large
    _ ≤ ‖T (a := a) (b := b) (c := c) (d := d) z‖ := h_low
