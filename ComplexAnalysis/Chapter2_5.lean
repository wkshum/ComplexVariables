/-

  Cross Ratio

-/

import Mathlib.Tactic
import ComplexAnalysis.Chapter2_2
import ComplexAnalysis.Chapter2_3
import ComplexAnalysis.Chapter2_4



noncomputable section CrossRatio

open EComplex LinearFracTrans


/-
Definition of cross ratio
-/
def cross_ratio (z0 z1 z2 z3 : EComplex) : EComplex :=
  match z1, z2, z3 with
  | EComplex.some z1, EComplex.some z2, EComplex.some z3 =>
    match z0 with
    | EComplex.some z0 => (z0 - z1) / (z0 - z3) * ((z2 - z3) / (z2 - z1))
    | none => (z2 - z3) / (z2 - z1)
  | none, EComplex.some z2, EComplex.some z3 =>
    (z2 - z3) / (z0 - z3)
  | EComplex.some z1, none, EComplex.some z3 =>
    (z0 - z1) / (z0 - z3)
  | EComplex.some z1, EComplex.some z2, none =>
    (z0 - z1) / (z2 - z1)
  | _, _, _ => none  -- junk value

/-
Verification theorems for the cross ratio definition, corresponding to the cases specified by the user.
These theorems confirm that the definition matches the standard formulas when the arguments are finite or one of them is infinity.
-/

theorem cross_ratio_finite (z0 z1 z2 z3 : ℂ) :
  cross_ratio z0 z1 z2 z3 = (z0 - z1) / (z0 - z3) * ((z2 - z3) / (z2 - z1)) := by
  rfl

theorem cross_ratio_z1_infty (z0 z2 z3 : ℂ) :
  cross_ratio z0 none z2 z3 = (z2 - z3) / (z0 - z3) := by
  rfl

theorem cross_ratio_z2_infty (z0 z1 z3 : ℂ) :
  cross_ratio z0 z1 none z3 = (z0 - z1) / (z0 - z3) := by
  rfl

theorem cross_ratio_z3_infty (z0 z1 z2 : ℂ) :
  cross_ratio z0 z1 z2 none = (z0 - z1) / (z2 - z1) := by
  rfl

/-! ## Cross ratio simplification lemmas the definition -/

-- All finite points
lemma cross_ratio_some (z0 z1 z2 z3 : ℂ) :
    cross_ratio (EComplex.some z0) (EComplex.some z1) (EComplex.some z2) (EComplex.some z3) =
    (EComplex.some z0 - EComplex.some z1) / (EComplex.some z0 - EComplex.some z3) * ((EComplex.some z2 - EComplex.some z3) / (EComplex.some z2 - EComplex.some z1)) := by
  simp only [cross_ratio]

-- z0 = ∞ (none)
lemma cross_ratio_none_z0 (z1 z2 z3 : ℂ) :
    cross_ratio none (EComplex.some z1) (EComplex.some z2) (EComplex.some z3) =
    (EComplex.some z2 - EComplex.some z3) / (EComplex.some z2 - EComplex.some z1) := by
  simp only [cross_ratio]

-- z1 = ∞ (none)
lemma cross_ratio_none_z1 (z0 z2 z3 : ℂ) :
    cross_ratio (EComplex.some z0) none (EComplex.some z2) (EComplex.some z3) =
    (EComplex.some z2 - EComplex.some z3) / (EComplex.some z0 - EComplex.some z3) := by
  simp only [cross_ratio]

-- z2 = ∞ (none)
lemma cross_ratio_none_z2 (z0 z1 z3 : ℂ) :
    cross_ratio (EComplex.some z0) (EComplex.some z1) none (EComplex.some z3) =
    (EComplex.some z0 - EComplex.some z1) / (EComplex.some z0 - EComplex.some z3) := by
  simp only [cross_ratio]

-- z3 = ∞ (none)
lemma cross_ratio_none_z3 (z0 z1 z2 : ℂ) :
    cross_ratio (EComplex.some z0) (EComplex.some z1) (EComplex.some z2) none =
    (EComplex.some z0 - EComplex.some z1) / (EComplex.some z2 - EComplex.some z1) := by
  simp only [cross_ratio]



/-! ## Extracting distinctness hypotheses from List.Pairwise -/

lemma pairwise_distinct_0_1 {z0 z1 z2 z3 : EComplex}
    (h : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) : z0 ≠ z1 := by
  rw [List.pairwise_cons] at h
  have h01 := h.left z1
  apply h01
  exact List.mem_cons_self


lemma pairwise_distinct_0_2 {z0 z1 z2 z3 : EComplex}
    (h : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) : z0 ≠ z2 := by
  rw [List.pairwise_cons] at h
  have h02 := h.left z2
  apply h02
  refine List.mem_cons_of_mem z1 ?_
  exact List.mem_cons_self


lemma pairwise_distinct_0_3 {z0 z1 z2 z3 : EComplex}
    (h : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) : z0 ≠ z3 := by
  rw [List.pairwise_cons] at h
  have h03 := h.left z3
  apply h03
  exact List.mem_of_getLast? rfl


lemma pairwise_distinct_1_2 {z0 z1 z2 z3 : EComplex}
    (h : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) : z1 ≠ z2 := by
  rw [List.pairwise_cons] at h
  have h_tail := h.right
  rw [List.pairwise_cons] at h_tail
  have h12 := h_tail.left z2
  apply h12
  exact List.mem_cons_self

lemma pairwise_distinct_1_3 {z0 z1 z2 z3 : EComplex}
    (h : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) : z1 ≠ z3 := by
  rw [List.pairwise_cons] at h
  have h_tail := h.right
  rw [List.pairwise_cons] at h_tail
  have h13 := h_tail.left z3
  apply h13
  exact List.mem_of_getLast? rfl

lemma pairwise_distinct_2_3 {z0 z1 z2 z3 : EComplex}
    (h : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) : z2 ≠ z3 := by
  rw [List.pairwise_cons] at h
  have h1 := h.right
  rw [List.pairwise_cons] at h1
  have h2 := h1.right
  rw [List.pairwise_cons] at h2
  have h23 := h2.left z3
  apply h23
  exact List.mem_singleton.mpr rfl



/-! ## Basic properties of cross ratio -/


lemma cross_ratio_some_eq (z0 z1 z2 z3 : ℂ)
    (h03 : z0 ≠ z3) (h21 : z2 ≠ z1) :
    cross_ratio (EComplex.some z0) (EComplex.some z1) (EComplex.some z2) (EComplex.some z3) =
    EComplex.some ((z0 - z1) / (z0 - z3) * ((z2 - z3) / (z2 - z1))) := by
  simp only [cross_ratio]
  rw [EComplex.sub_some, EComplex.sub_some, EComplex.sub_some, EComplex.sub_some]
  rw [EComplex.div_some (sub_ne_zero.mpr h03)]
  rw [EComplex.div_some (sub_ne_zero.mpr h21)]
  rw [EComplex.mul_some]

lemma cross_ratio_none_z0_eq (z1 z2 z3 : ℂ) (h21 : z2 ≠ z1) :
    cross_ratio none (EComplex.some z1) (EComplex.some z2) (EComplex.some z3) =
    EComplex.some ((z2 - z3) / (z2 - z1)) := by
  simp only [cross_ratio]
  rw [EComplex.sub_some, EComplex.sub_some]
  rw [EComplex.div_some (sub_ne_zero.mpr h21)]

lemma cross_ratio_none_z1_eq (z0 z2 z3 : ℂ) (h03 : z0 ≠ z3) :
    cross_ratio (EComplex.some z0) none (EComplex.some z2) (EComplex.some z3) =
    EComplex.some ((z2 - z3) / (z0 - z3)) := by
  simp only [cross_ratio]
  rw [EComplex.sub_some, EComplex.sub_some]
  rw [EComplex.div_some (sub_ne_zero.mpr h03)]

lemma cross_ratio_none_z2_eq (z0 z1 z3 : ℂ) (h03 : z0 ≠ z3) :
    cross_ratio (EComplex.some z0) (EComplex.some z1) none (EComplex.some z3) =
    EComplex.some ((z0 - z1) / (z0 - z3)) := by
  simp only [cross_ratio]
  rw [EComplex.sub_some, EComplex.sub_some]
  rw [EComplex.div_some (sub_ne_zero.mpr h03)]

lemma cross_ratio_none_z3_eq (z0 z1 z2 : ℂ) (h21 : z2 ≠ z1) :
    cross_ratio (EComplex.some z0) (EComplex.some z1) (EComplex.some z2) none =
    EComplex.some ((z0 - z1) / (z2 - z1)) := by
  simp only [cross_ratio]
  rw [EComplex.sub_some, EComplex.sub_some]
  rw [EComplex.div_some (sub_ne_zero.mpr h21)]




/-! ## Core algebraic identity for invariance -/

-- The key identity: after applying LFT, cross ratio formula simplifies
-- Using your formula: (z0-z1)/(z0-z3) * (z2-z3)/(z2-z1)

lemma cross_ratio_lft_num_denom (f : LinearFracTrans) (z0 z1 z2 z3 : ℂ)
    (h0 : f.c * z0 + f.d ≠ 0) (h1 : f.c * z1 + f.d ≠ 0)
    (h2 : f.c * z2 + f.d ≠ 0) (h3 : f.c * z3 + f.d ≠ 0) :
    let fz0 := (f.a * z0 + f.b) / (f.c * z0 + f.d)
    let fz1 := (f.a * z1 + f.b) / (f.c * z1 + f.d)
    let fz2 := (f.a * z2 + f.b) / (f.c * z2 + f.d)
    let fz3 := (f.a * z3 + f.b) / (f.c * z3 + f.d)
    (fz0 - fz1) / (fz0 - fz3) * ((fz2 - fz3) / (fz2 - fz1)) =
    (z0 - z1) / (z0 - z3) * ((z2 - z3) / (z2 - z1)) := by
  -- Use apply_sub_apply on each difference
  have det := f.determinant_ne_zero
  simp only []
  rw [apply_sub_apply f z0 z1 h0 h1]
  rw [apply_sub_apply f z0 z3 h0 h3]
  rw [apply_sub_apply f z2 z3 h2 h3]
  rw [apply_sub_apply f z2 z1 h2 h1]
  have hp01 : (f.c * z0 + f.d) * (f.c * z1 + f.d) ≠ 0 := mul_ne_zero h0 h1
  have hp03 : (f.c * z0 + f.d) * (f.c * z3 + f.d) ≠ 0 := mul_ne_zero h0 h3
  have hp23 : (f.c * z2 + f.d) * (f.c * z3 + f.d) ≠ 0 := mul_ne_zero h2 h3
  have hp21 : (f.c * z2 + f.d) * (f.c * z1 + f.d) ≠ 0 := mul_ne_zero h2 h1
  field_simp [det, hp01, hp03, hp23, hp21]





/--  #### Theorem 2.5.2
The cross ratio of four points in the extended complex
plane is invariant under any linear fractional
transformation (Möbius transformation). For any
four points z₁, z₂, z₃, z₄ ∈ ℂ∞ and any
LFT f(z) = (a z + b) / (c z + d) with ad - bc ≠ 0,
we have cross_ratio (f z₁) (f z₂) (f z₃) (f z₄)
= cross_ratio z₁ z₂ z₃ z₄.
-/
theorem cross_ratio_invariant (f : LinearFracTrans)
    (z0 z1 z2 z3 : EComplex)
    (h_distinct : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) :
    cross_ratio (f z0) (f z1) (f z2) (f z3) =
    cross_ratio z0 z1 z2 z3 := by
  have h01 : z0 ≠ z1 := pairwise_distinct_0_1 h_distinct
  have h02 : z0 ≠ z2 := pairwise_distinct_0_2 h_distinct
  have h03 : z0 ≠ z3 := pairwise_distinct_0_3 h_distinct
  have h12 : z1 ≠ z2 := pairwise_distinct_1_2 h_distinct
  have h13 : z1 ≠ z3 := pairwise_distinct_1_3 h_distinct
  have h23 : z2 ≠ z3 := pairwise_distinct_2_3 h_distinct
  -- Split on c = 0 vs c ≠ 0
  by_cases hc : f.c = 0
  ·-- ═══════════════════════════════════════════════════════════════
   -- CASE A: c = 0 (affine transformation)
   -- f(z) = (a/d)z + (b/d), f(∞) = ∞
   -- ═══════════════════════════════════════════════════════════════
   --establish d ≠ 0
    have hd : f.d ≠ 0 := by
      intro hd_zero
      have := f.determinant_ne_zero
      simp only [hc,hd_zero,mul_zero,sub_zero] at this
      exact false_of_ne this
    --Also a ≠ 0
    have ha : f.a ≠ 0 := by
      intro ha_zero
      have := f.determinant_ne_zero
      simp only [hc,ha_zero,zero_mul,mul_zero,zero_sub,neg_zero] at this
      exact false_of_ne this
    --Lemma : apply when c = 0 and z is finite
    have apply_affine_finite : ∀ w : ℂ , f (EComplex.some w) = EComplex.some ((f.a / f.d) * w + (f.b / f.d)) := by
      intro w
      simp only [LinearFracTrans.apply, hc, ↓reduceIte]

    --Lemma : apply when c = 0 and z is ∞
    have apply_affine_inf : f none = none := by
      simp only [LinearFracTrans.apply, hc, ↓reduceIte]
    have affine_sub : ∀ w1 w2 : ℂ,
         (f.a / f.d) * w1 + (f.b / f.d) - ((f.a / f.d) * w2 + (f.b / f.d)) =
         (f.a / f.d) * (w1 - w2) := by
      intro w1 w2
      ring
    -- Now case split on which points are ∞
    match z0, z1, z2, z3 with
    | EComplex.some w0, EComplex.some w1, EComplex.some w2, EComplex.some w3 =>
      --all Finite
      simp only [ne_eq] at h01 h02 h03 h12 h13 h23
      rw [apply_affine_finite w0, apply_affine_finite w1,
          apply_affine_finite w2, apply_affine_finite w3]
      rw [cross_ratio_some_eq, cross_ratio_some_eq]
      have had : f.a / f.d ≠ 0 := div_ne_zero ha hd
      simp only [affine_sub]
      field_simp [had]
      exact coe_ne_coe_iff.mp h03
      exact coe_ne_coe_iff.mp fun a ↦ h12 (id (Eq.symm a))
      intro heq
      field_simp at heq
      rw [add_right_cancel_iff,mul_comm,mul_comm f.a w3] at heq
      have h_eq : w0 = w3 := by exact mul_right_cancel₀ ha heq
      exact Ne.elim h03 (congrArg EComplex.some h_eq)
      intro heq
      field_simp at heq
      rw [add_right_cancel_iff,mul_comm,mul_comm f.a w1] at heq
      have h_eq : w2 = w1 := by exact mul_right_cancel₀ ha heq
      exact Ne.elim h12 (congrArg EComplex.some (id (Eq.symm h_eq)))

    | none, EComplex.some w1, EComplex.some w2, EComplex.some w3 =>
      -- z0 = ∞
      simp only [ne_eq] at h12 h13 h23
      rw [apply_affine_inf, apply_affine_finite w1,
          apply_affine_finite w2, apply_affine_finite w3]
      rw [cross_ratio_none_z0_eq, cross_ratio_none_z0_eq]
      -- Goal: (a/d)(w2-w3) / (a/d)(w2-w1) = (w2-w3) / (w2-w1)
      have had : f.a / f.d ≠ 0 := div_ne_zero ha hd
      simp only [affine_sub]
      field_simp [had]
      exact coe_ne_coe_iff.mp fun a ↦ h12 (id (Eq.symm a))
      intro heq
      field_simp at heq
      rw [add_right_cancel_iff,mul_comm,mul_comm f.a w1] at heq
      have h_eq : w2 = w1 := by exact mul_right_cancel₀ ha heq
      exact Ne.elim h12 (congrArg EComplex.some (id (Eq.symm h_eq)))
    | EComplex.some w0, none, EComplex.some w2, EComplex.some w3 =>
      -- z1 = ∞
      simp only [ne_eq] at h02 h03 h23
      rw [apply_affine_inf, apply_affine_finite w0,
          apply_affine_finite w2, apply_affine_finite w3]
      rw [cross_ratio_none_z1_eq, cross_ratio_none_z1_eq]
      congr 1
      field_simp
      have w03_neq0 : w0 - w3 ≠ 0 :=
        by exact sub_ne_zero_of_ne fun a ↦ h03 (congrArg EComplex.some a)
      have denomi_neq0 :  (f.a * w0 + f.b - (f.a * w3 + f.b)) ≠ 0 := by {
        intro heq
        ring_nf at heq
        rw[sub_eq_zero,mul_comm,mul_comm _ w3] at heq
        have w01_eq : w0 = w3 := by exact mul_right_cancel₀ ha heq
        exact Ne.elim h03 (congrArg EComplex.some w01_eq)
      }
      field_simp [w03_neq0,denomi_neq0]
      ring_nf
      exact coe_ne_coe_iff.mp h03
      intro heq
      field_simp at heq
      rw[add_right_cancel_iff,mul_comm,mul_comm f.a w3] at heq
      have h_eq : w0 = w3 := by exact mul_right_cancel₀ ha heq
      exact Ne.elim h03 (congrArg EComplex.some h_eq)

    | EComplex.some w0, EComplex.some w1, none, EComplex.some w3 =>
      -- z2 = ∞
      simp only [ne_eq] at h01 h03 h13
      rw [apply_affine_inf, apply_affine_finite w0,
          apply_affine_finite w1, apply_affine_finite w3]
      rw [cross_ratio_none_z2_eq, cross_ratio_none_z2_eq]
      congr 1
      field_simp
      have w03_neq0 : w0 - w3 ≠ 0
        := by exact sub_ne_zero_of_ne fun a ↦ h03 (congrArg EComplex.some a)
      have denomi1_neq0 : (f.a * w0 + f.b - (f.a * w3 + f.b)) ≠ 0 := by
        intro heq
        ring_nf at heq
        rw[sub_eq_zero, mul_comm, mul_comm _ w3] at heq
        have h_eq : w0 = w3 := by exact mul_right_cancel₀ ha heq
        exact Ne.elim h03 (congrArg EComplex.some h_eq)
      field_simp[w03_neq0,denomi1_neq0]
      ring_nf
      exact coe_ne_coe_iff.mp h03
      intro heq
      field_simp at heq
      rw[add_right_cancel_iff,mul_comm,mul_comm f.a w3] at heq
      have h_eq : w0 = w3 := by exact mul_right_cancel₀ ha heq
      exact Ne.elim h03 (congrArg EComplex.some h_eq)

      -- Goal: (f(w0) - f(w1)) / (f(w0) - f(w3)) = (w0-w1) / (w0-w3)

    | EComplex.some w0, EComplex.some w1, EComplex.some w2, none =>
      -- z3 = ∞
      simp only [ne_eq] at h01 h02 h12
      rw [apply_affine_inf, apply_affine_finite w0,
          apply_affine_finite w1, apply_affine_finite w2]
      rw [cross_ratio_none_z3_eq, cross_ratio_none_z3_eq]
      -- Goal: (f(w0) - f(w1)) / (a/d)(w2-w1) = (w0-w1) / (w2-w1)
      congr 1
      field_simp
      have w21_neq0 : w2 - w1 ≠ 0
        := by exact sub_ne_zero_of_ne fun a ↦ h12 (congrArg EComplex.some (id (Eq.symm a)))
      have denomi1 : (f.a * w2 + f.b - (f.a * w1 + f.b)) ≠ 0 := by
        intro heq
        ring_nf at heq
        rw[sub_eq_zero, mul_comm, mul_comm _ w1] at heq
        have h_eq : w2 = w1 := by exact mul_right_cancel₀ ha heq
        exact Ne.elim h12 (congrArg EComplex.some (id (Eq.symm h_eq)))
      field_simp[w21_neq0,denomi1]
      ring_nf
      exact coe_ne_coe_iff.mp fun a ↦ h12 (id (Eq.symm a))
      intro heq
      field_simp at heq
      rw[add_right_cancel_iff,mul_comm,mul_comm f.a w1] at heq
      have h_eq : w2 = w1 := by exact mul_right_cancel₀ ha heq
      exact Ne.elim h12 (congrArg EComplex.some (id (Eq.symm h_eq)))

    -- Impossible cases: two or more ∞
    | none, none, _, _ => exact absurd rfl h01
    | none, _, none, _ => exact absurd rfl h02
    | none, _, _, none => exact absurd rfl h03
    | _, none, none, _ => exact absurd rfl h12
    | _, none, _, none => exact absurd rfl h13
    | _, _, none, none => exact absurd rfl h23


  ·-- ═══════════════════════════════════════════════════════════════
   -- CASE B: c ≠ 0 (full Möbius transformation)
   -- f(z) = (az+b)/(cz+d), f(∞) = a/c, f(-d/c) = ∞
   -- ═══════════════════════════════════════════════════════════════

    match z0, z1, z2, z3 with

    -- ─────────────────────────────────────────────────────────────
    -- CASE B.1: All four points are finite
    -- ─────────────────────────────────────────────────────────────
    | EComplex.some w0, EComplex.some w1, EComplex.some w2, EComplex.some w3 =>
      have h01 : w0 ≠ w1 := by exact_mod_cast h01
      have h02 : w0 ≠ w2 := by exact_mod_cast h02
      have h03 : w0 ≠ w3 := by exact_mod_cast h03
      have h12 : w1 ≠ w2 := by exact_mod_cast h12
      have h13 : w1 ≠ w3 := by exact_mod_cast h13
      have h23 : w2 ≠ w3 := by exact_mod_cast h23

      -- Helper lemmas for this case
      -- Apply to finite point not at pole
      have apply_finite : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f (EComplex.some w) = EComplex.some ((f.a * w + f.b) / (f.c * w + f.d)) := by
        intro w hw
        push Not at hc
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have condition1 : w ≠ -f.d / f.c := by
          intro heq
          field_simp at heq
          rw[eq_neg_iff_add_eq_zero, mul_comm] at heq
          exact Ne.elim hw heq
        simp [condition1]


      -- Apply to point at pole gives ∞
      have apply_pole : ∀ w : ℂ, f.c * w + f.d = 0
        → f (EComplex.some w) = none := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have : w = -f.d / f.c := by
          field_simp
          rw[eq_neg_iff_add_eq_zero, mul_comm]
          exact hw
        simp [this]

      -- Apply to ∞ gives a/c
      have apply_inf : f none = EComplex.some (f.a / f.c) := by
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]


      have apply_sub : ∀ w1 w2 : ℂ, f.c * w1 + f.d ≠ 0 → f.c * w2 + f.d ≠ 0 →
          (f.a * w1 + f.b) / (f.c * w1 + f.d) - (f.a * w2 + f.b) / (f.c * w2 + f.d) =
          (f.a * f.d - f.b * f.c) * (w1 - w2) / ((f.c * w1 + f.d) * (f.c * w2 + f.d)) := by
        intro w1 w2 hw1 hw2
        rw [div_sub_div _ _ hw1 hw2]
        congr 1
        ring


      -- Sub-cases: is any point at the pole -d/c?
      by_cases hp0 : f.c * w0 + f.d = 0
      ·-- CASE B.1.a: w0 is at the pole, so f(w0) = ∞
        rw [apply_pole w0 hp0]
        -- f(w0) = ∞, so we use cross_ratio_none_z0_eq for LHS

        -- w1, w2, w3 cannot be at pole (distinct from w0)
        have hp1 : f.c * w1 + f.d ≠ 0 := by
          intro h
          have this1 : w1 = -f.d / f.c := by
            field_simp
            rw[eq_neg_iff_add_eq_zero, mul_comm]
            exact h
          have this2 : w0 = -f.d / f.c := by
            field_simp
            rw[eq_neg_iff_add_eq_zero, mul_comm]
            exact hp0
          rw [← this1] at this2
          (expose_names; exact Ne.elim h01_1
            (congrArg EComplex.some this2))
        have hp2 : f.c * w2 + f.d ≠ 0 := by
          intro h
          have this1 : w2 = -f.d / f.c := by
            field_simp
            rw[eq_neg_iff_add_eq_zero, mul_comm]
            exact h
          have this2 : w0 = -f.d / f.c := by
            field_simp
            rw[eq_neg_iff_add_eq_zero, mul_comm]
            exact hp0
          rw [← this1] at this2
          (expose_names; exact Ne.elim h02_1
            (congrArg EComplex.some this2))
        have hp3 : f.c * w3 + f.d ≠ 0 := by
          intro h
          have this1 : w3 = -f.d / f.c := by
            field_simp
            rw[eq_neg_iff_add_eq_zero, mul_comm]
            exact h
          have this2 : w0 = -f.d / f.c := by
            field_simp
            rw[eq_neg_iff_add_eq_zero, mul_comm]
            exact hp0
          rw [← this1] at this2
          (expose_names; exact Ne.elim h03_1 (congrArg EComplex.some this2))
        rw [apply_finite w1 hp1, apply_finite w2 hp2, apply_finite w3 hp3]
        rw [cross_ratio_none_z0_eq, cross_ratio_some_eq]
        rw [apply_sub w2 w3 hp2 hp3, apply_sub w2 w1 hp2 hp1]
        have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
        have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
        have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
        have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
        have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
        have hprod23 : (f.c * w2 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp2 hp3
        have hprod21 : (f.c * w2 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp2 hp1
        field_simp [hdet, hdiff23, hdiff21, hdiff01, hdiff03, hprod23, hprod21]
        congr 1
        have denomi1 : ((f.c * w3 + f.d) * (w2 - w1)) ≠ 0 := by
          apply mul_ne_zero
          exact hp3
          exact hdiff21
        have denomi2 : ((w2 - w1) * (w0 - w3)) ≠ 0 := by
          apply mul_ne_zero
          exact hdiff21
          exact hdiff03
        field_simp [denomi1, denomi2]
        have denomi3 : (w3 * f.c + f.d) ≠ 0 := by
          rw [mul_comm]
          exact hp3
        field_simp [denomi3]
        have hw0 : w0 = -f.d / f.c := by
          field_simp
          rw [eq_neg_iff_add_eq_zero,mul_comm]
          exact hp0
        rw [hw0]
        field_simp [hc]
        ring_nf
        exact h03
        exact h12.symm
        intro heq
        field_simp [hp2,hp1] at heq
        rw [mul_comm] at hp2
        field_simp [hp2] at heq
        ring_nf at heq
        simp only [add_left_inj] at heq
        have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
        have heq_sub :  f.a * w2 * f.d + f.b * f.c * w1 =  f.a * w1 * f.d + w2 * f.b * f.c := by
          apply sub_eq_zero.mp
          calc
            f.a * w2 * f.d + f.b * f.c * w1 - (f.a * w1 * f.d + w2 * f.b * f.c)
                =(f.a * w2 * f.d + f.b * f.c * w1 + f.a * w2 * f.c * w1) - (f.a * w1 * f.d + w2 * f.b
                * f.c + f.a * w2 * f.c * w1) := by ring_nf
            _ = (f.a * w2 * f.c * w1 + f.a * w2 * f.d + f.b * f.c * w1) - (f.a * w2 * f.c * w1 + f.a
            * w1 * f.d + w2 * f.b * f.c) := by ring_nf
            _ = 0 := by rw [heq,sub_self]
        have h_factor : (f.a * f.d - f.b * f.c) * (w2 - w1) = 0 := by
          apply sub_eq_zero.mp
          rw [sub_zero]
          calc
            (f.a * f.d - f.b * f.c) * (w2 - w1)
               = (f.a * f.d) * (w2 - w1) - (f.b * f.c) * (w2 - w1) := by ring_nf
            _ = (f.a * w2 * f.d + f.b * f.c * w1) - (f.a * w1 * f.d + w2 * f.b * f.c) := by ring_nf
            _ = 0 := by rw[heq_sub, sub_self]
        have hw_ne : w2 - w1 ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h12))
        apply mul_ne_zero at h_factor
        exact h_factor
        exact hdet
        exact hw_ne

      · by_cases hp1 : f.c * w1 + f.d = 0

        ·-- CASE B.1.b: w1 is at the pole, so f(w1) = ∞
          rw [apply_pole w1 hp1]
          have hp0' : f.c * w0 + f.d ≠ 0 := hp0
          have hp2 : f.c * w2 + f.d ≠ 0 := by
            intro h
            have this1 : w2 = -f.d / f.c := by
             field_simp [hc]
             rw [eq_neg_iff_add_eq_zero, mul_comm w2 _]
             exact h
            have this2 : w1 = -f.d / f.c := by
              field_simp [hc]
              rw [eq_neg_iff_add_eq_zero, mul_comm w1 _]
              exact hp1
            rw [← this1] at this2
            (expose_names; exact Ne.elim h12_1
              (congrArg EComplex.some this2))
          have hp3 : f.c * w3 + f.d ≠ 0 := by
            intro h
            have this1 : w3 = -f.d / f.c := by
              field_simp
              rw[eq_neg_iff_add_eq_zero, mul_comm]
              exact h
            have this2 : w1 = -f.d / f.c := by
              field_simp [hc]
              rw [eq_neg_iff_add_eq_zero, mul_comm w1 _]
              exact hp1
            rw [← this1] at this2
            (expose_names; exact Ne.elim h13_1 (congrArg EComplex.some this2))
          rw [apply_finite w0 hp0', apply_finite w2 hp2, apply_finite w3 hp3]
          rw [cross_ratio_none_z1_eq,cross_ratio_some_eq]
          congr 1
          rw [apply_sub w2 w3 hp2 hp3, apply_sub w0 w3 hp0' hp3]
          have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
          have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
          have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
          have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
          have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
          have hprod23 : (f.c * w2 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp2 hp3
          have hprod03 : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0' hp3
          have hw1 : w1 = -f.d / f.c := by
            field_simp [hc] at hp1
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact hp1
          rw [hw1]
          field_simp [hc, hdet,hprod23,hprod03]
          have denomi2 : (f.c * w2 - -f.d) ≠ 0 := by
            intro heq
            simp only [sub_neg_eq_add] at heq
            exact Ne.elim hp2 heq
          field_simp [denomi2]
          ring_nf
          (expose_names; exact coe_ne_coe_iff.mp h03_1)
          (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
          intro heq
          field_simp at heq
          have denomi3 : (w0 * f.c + f.d) ≠ 0 := by
            rw [mul_comm]
            exact hp0'
          field_simp at heq
          ring_nf at heq
          have heq' : (f.a * f.d - f.b * f.c) * (w0 - w3) = 0 := by
            calc (f.a * f.d - f.b * f.c) * (w0 - w3)
                = f.a * w0 * f.d + f.b * f.c * w3 - f.a * w3 * f.d - w0 * f.b * f.c := by ring
              _ = (f.a * w0 * f.c * w3 + f.a * w0 * f.d + f.b * f.c * w3 + f.b * f.d) -
                  (f.a * w0 * f.c * w3 + f.a * w3 * f.d + w0 * f.b * f.c + f.b * f.d) := by ring
              _ = 0 := by rw [heq]; ring
          rcases mul_eq_zero.mp heq' with hdet | hdiff
          · have hdet1 : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            contradiction
          · exact h03 (sub_eq_zero.mp hdiff)
        · by_cases hp2 : f.c * w2 + f.d = 0

          ·-- CASE B.1.c: w2 is at the pole, so f(w2) = ∞
            rw [apply_pole w2 hp2]

            have hp0' : f.c * w0 + f.d ≠ 0 := hp0
            have hp1' : f.c * w1 + f.d ≠ 0 := hp1
            have hp3 : f.c * w3 + f.d ≠ 0 := by
              intro h
              have this1 : w3 = -f.d / f.c  := by
                field_simp
                rw [eq_neg_iff_add_eq_zero,mul_comm]
                exact h
              have this2 : w2 = -f.d / f.c := by
                field_simp
                rw [eq_neg_iff_add_eq_zero,mul_comm]
                exact hp2
              rw [←this1] at this2
              (expose_names; exact Ne.elim h23_1 (congrArg EComplex.some this2))
            rw [apply_finite w0 hp0', apply_finite w1 hp1', apply_finite w3 hp3]
            rw [cross_ratio_none_z2_eq, cross_ratio_some_eq]
            rw [apply_sub w0 w1 hp0' hp1', apply_sub w0 w3 hp0' hp3]
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
            have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
            have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
            have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
            have hprod01 : (f.c * w0 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp0' hp1'
            have hprod03 : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0' hp3
            have hw2 : w2 = -f.d / f.c := by
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact hp2
            congr 1
            rw [hw2]
            field_simp [hc,hdet,hprod01,hprod03]
            have hne : -f.d - f.c * w1 ≠ 0 := by
              intro h
              apply hp1'
              have : f.c * w1 + f.d = -(-f.d - f.c * w1) := by ring
              rw [this, h, neg_zero]
            field_simp [hne]
            ring_nf
            (expose_names; exact coe_ne_coe_iff.mp h03_1)
            (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
            rw [ne_eq, ← sub_eq_zero, apply_sub w0 w3 hp0' hp3]
            exact div_ne_zero (mul_ne_zero f.determinant_ne_zero (sub_ne_zero.mpr h03)) (mul_ne_zero hp0' hp3)

          · by_cases hp3 : f.c * w3 + f.d = 0

            ·-- CASE B.1.d: w3 is at the pole, so f(w3) = ∞
              rw [apply_pole w3 hp3]
              have hp0' : f.c * w0 + f.d ≠ 0 := hp0
              have hp1' : f.c * w1 + f.d ≠ 0 := hp1
              have hp2' : f.c * w2 + f.d ≠ 0 := hp2
              rw [apply_finite w0 hp0', apply_finite w1 hp1', apply_finite w2 hp2']
              rw [cross_ratio_none_z3_eq, cross_ratio_some_eq]
              rw [apply_sub w0 w1 hp0' hp1', apply_sub w2 w1 hp2' hp1']
              have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
              have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
              have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
              have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
              have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
              have hprod01 : (f.c * w0 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp0' hp1'
              have hprod21 : (f.c * w2 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp2' hp1'
              have hw3 : w3 = -f.d / f.c := by
                field_simp
                rw [eq_neg_iff_add_eq_zero,mul_comm]
                exact hp3
              congr 1
              rw [hw3]
              field_simp [hc, hdet, hprod01, hprod21]
              simp only [sub_neg_eq_add]
              field_simp [hp0']
              (expose_names; exact coe_ne_coe_iff.mp h03_1)
              (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
              rw [ne_eq, ← sub_eq_zero, apply_sub w2 w1 hp2' hp1']
              exact div_ne_zero (mul_ne_zero f.determinant_ne_zero (sub_ne_zero.mpr h12.symm)) (mul_ne_zero hp2' hp1')


            ·-- CASE B.1.e: No point is at the pole
              -- All four map to finite values
              -- This is the main computational case
              rw [apply_finite w0 hp0, apply_finite w1 hp1,
                  apply_finite w2 hp2, apply_finite w3 hp3]
              rw [cross_ratio_some_eq, cross_ratio_some_eq]
              rw [apply_sub w0 w1 hp0 hp1, apply_sub w0 w3 hp0 hp3,
                  apply_sub w2 w3 hp2 hp3, apply_sub w2 w1 hp2 hp1]
              have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
              have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
              have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
              have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
              have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
              have hprod01 : (f.c * w0 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp0 hp1
              have hprod03 : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0 hp3
              have hprod23 : (f.c * w2 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp2 hp3
              have hprod21 : (f.c * w2 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp2 hp1
              field_simp [hdet, hprod01, hprod03, hprod23, hprod21]
              (expose_names; exact coe_ne_coe_iff.mp h03_1)
              (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
              rw [ne_eq, ← sub_eq_zero, apply_sub w0 w3 hp0 hp3]
              exact div_ne_zero (mul_ne_zero f.determinant_ne_zero (sub_ne_zero.mpr h03)) (mul_ne_zero hp0 hp3)
              rw [ne_eq, ← sub_eq_zero, apply_sub w2 w1 hp2 hp1]
              exact div_ne_zero (mul_ne_zero f.determinant_ne_zero (sub_ne_zero.mpr h12.symm)) (mul_ne_zero hp2 hp1)
    -- ─────────────────────────────────────────────────────────────
    -- CASE B.2: z0 = ∞, others finite
    -- ─────────────────────────────────────────────────────────────
    | none, EComplex.some w1, EComplex.some w2, EComplex.some w3 =>
      have h12 : w1 ≠ w2 := by exact_mod_cast h12
      have h13 : w1 ≠ w3 := by exact_mod_cast h13
      have h23 : w2 ≠ w3 := by exact_mod_cast h23


      -- f(∞) = a/c
      have apply_inf : f none = EComplex.some (f.a / f.c) := by
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]


      -- Apply to finite point not at pole
      have apply_finite : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f (EComplex.some w) = EComplex.some ((f.a * w + f.b) / (f.c * w + f.d)) := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have condiction_ne : w ≠ -f.d / f.c := by
          intro heq
          field_simp at heq
          rw[eq_neg_iff_add_eq_zero,mul_comm] at heq
          contradiction
        simp [condiction_ne]
        -- congr 1

      -- Apply to point at pole gives ∞
      have apply_pole : ∀ w : ℂ, f.c * w + f.d = 0 → f (EComplex.some w) = none := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have : w = -f.d / f.c := by
          field_simp [hc] at hw
          field_simp [hc]
          rw[eq_neg_iff_add_eq_zero,mul_comm]
          exact hw
        simp [this]

      -- Key: difference f(∞) - f(w) = (a/c) - f(w)
      have apply_inf_sub : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f.a / f.c - (f.a * w + f.b) / (f.c * w + f.d) =
          (f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
        intro w hw
        have hc' : f.c ≠ 0 := hc
        field_simp [hc', hw]
        ring

      -- Key: difference of two finite images
      have apply_sub : ∀ w1 w2 : ℂ, f.c * w1 + f.d ≠ 0 → f.c * w2 + f.d ≠ 0 →
          (f.a * w1 + f.b) / (f.c * w1 + f.d) - (f.a * w2 + f.b) / (f.c * w2 + f.d) =
          (f.a * f.d - f.b * f.c) * (w1 - w2) / ((f.c * w1 + f.d) * (f.c * w2 + f.d)) := by
        intro w1 w2 hw1 hw2
        rw [div_sub_div _ _ hw1 hw2]
        congr 1
        ring

      -- f(∞) = a/c, need to check if any wi is at the pole
      by_cases hp1 : f.c * w1 + f.d = 0

      ·-- CASE B.2.a: w1 is at the pole
        rw [apply_inf, apply_pole w1 hp1]
        have hp2 : f.c * w2 + f.d ≠ 0 := by
          intro h
          have this1 : w2 = -f.d / f.c := by
            field_simp [hc] at h
            field_simp
            rw[eq_neg_iff_add_eq_zero,mul_comm]
            exact h
          have this2 : w1 = -f.d / f.c := by
            field_simp [hc] at hp1
            field_simp
            rw[eq_neg_iff_add_eq_zero,mul_comm]
            exact hp1
          rw [← this1] at this2
          contradiction
        have hp3 : f.c * w3 + f.d ≠ 0 := by
          intro h
          have this1 : w3 = -f.d / f.c := by
            field_simp [hc]
            rw[eq_neg_iff_add_eq_zero,mul_comm]
            exact h
          have this2 : w1 = -f.d / f.c := by
            field_simp [hc]
            rw[eq_neg_iff_add_eq_zero,mul_comm]
            exact hp1
          rw [← this1] at this2
          contradiction
        rw [apply_finite w2 hp2, apply_finite w3 hp3]
        rw [cross_ratio_none_z1_eq, cross_ratio_none_z0_eq]
        rw [apply_sub w2 w3 hp2 hp3, apply_inf_sub w3 hp3]
        have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
        have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
        have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
        have hprod23 : (f.c * w2 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp2 hp3
        have hw1 : w1 = -f.d / f.c := by
          field_simp [hc]
          rw[eq_neg_iff_add_eq_zero,mul_comm]
          exact hp1
        congr 1
        field_simp [hc, hdet, hprod23]
        rw [hw1]
        field_simp [hc]
        ring_nf
        (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
        rw [ne_eq, ← sub_eq_zero, apply_inf_sub w3 hp3]
        exact div_ne_zero f.determinant_ne_zero (mul_ne_zero hc hp3)

      · by_cases hp2 : f.c * w2 + f.d = 0

        ·-- CASE B.2.b: w2 is at the pole
          rw [apply_inf, apply_pole w2 hp2]
          have hp1' : f.c * w1 + f.d ≠ 0 := hp1
          have hp3 : f.c * w3 + f.d ≠ 0 := by
            intro h
            have this1 : w3 = -f.d / f.c := by
              field_simp [hc] at h
              field_simp
              rw[eq_neg_iff_add_eq_zero,mul_comm]
              exact h
            have this2 : w2 = -f.d / f.c := by
              field_simp [hc] at hp2
              field_simp
              rw[eq_neg_iff_add_eq_zero,mul_comm]
              exact hp2
            rw [← this1] at this2
            contradiction
          rw [apply_finite w1 hp1', apply_finite w3 hp3]
          rw [cross_ratio_none_z2_eq, cross_ratio_none_z0_eq]
          rw [apply_inf_sub w1 hp1', apply_inf_sub w3 hp3]
          have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
          have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
          have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
          have hw2 : w2 = -f.d / f.c := by
            field_simp [hc] at hp2
            field_simp
            rw[eq_neg_iff_add_eq_zero,mul_comm]
            exact hp2
          field_simp [hc, hdet]
          rw [hw2]
          congr 1
          field_simp
          have h_denom_ne_zero : -f.d - f.c * w1 ≠ 0 := by
            intro hzero
            apply hp1
            calc
              f.c * w1 + f.d = -(-f.d - f.c * w1) := by ring
              _ = -0 := by rw [hzero]
              _ = 0 := by ring_nf
          field_simp [h_denom_ne_zero]
          ring_nf
          (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
          have h_det_ne_zero : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
          have h_diff_ne_zero : f.a / f.c - (f.a * w3 + f.b) / (f.c * w3 + f.d) ≠ 0 := by
            rw [apply_inf_sub w3 hp3]
            refine div_ne_zero h_det_ne_zero ?_
            exact mul_ne_zero (by exact hc) hp3
          intro heq
          apply h_diff_ne_zero
          rw [heq, sub_self]

        · by_cases hp3 : f.c * w3 + f.d = 0

          ·-- CASE B.2.c: w3 is at the pole
            rw [apply_inf, apply_pole w3 hp3]
            have hp1' : f.c * w1 + f.d ≠ 0 := hp1
            have hp2' : f.c * w2 + f.d ≠ 0 := hp2
            rw [apply_finite w1 hp1', apply_finite w2 hp2']
            rw [cross_ratio_none_z3_eq, cross_ratio_none_z0_eq]
            rw [apply_inf_sub w1 hp1', apply_sub w2 w1 hp2' hp1']
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
            have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
            have hprod21 : (f.c * w2 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp2' hp1'
            have hw3 : w3 = -f.d / f.c := by
              field_simp [hc] at hp3
              field_simp
              rw[eq_neg_iff_add_eq_zero,mul_comm]
              exact hp3
            field_simp [hc, hdet, hprod21]
            rw [hw3]
            congr 1
            field_simp
            ring_nf
            (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff_ne_zero : ((f.a * w2 + f.b) / (f.c * w2 + f.d)) - ((f.a * w1 + f.b) / (f.c * w1 + f.d)) ≠ 0 := by
              rw [apply_sub w2 w1 hp2' hp1']
              refine div_ne_zero ?_ (mul_ne_zero hp2' hp1')
              exact mul_ne_zero hdet (sub_ne_zero.mpr h12.symm)
            intro heq
            apply hdiff_ne_zero
            rw [heq, sub_self]

          ·-- CASE B.2.d: No pole among w1, w2, w3
            rw [apply_inf, apply_finite w1 hp1, apply_finite w2 hp2, apply_finite w3 hp3]
            rw [cross_ratio_some_eq, cross_ratio_none_z0_eq]
            rw [apply_inf_sub w1 hp1, apply_inf_sub w3 hp3,
                apply_sub w2 w3 hp2 hp3, apply_sub w2 w1 hp2 hp1]
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
            have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
            have hprod23 : (f.c * w2 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp2 hp3
            have hprod21 : (f.c * w2 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp2 hp1
            field_simp [hc, hdet, hprod23, hprod21]
            (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff_ne_zero : f.a / f.c - (f.a * w3 + f.b) / (f.c * w3 + f.d) ≠ 0 := by
              rw [apply_inf_sub w3 hp3]
              refine div_ne_zero hdet ?_
              refine mul_ne_zero ?_ hp3
              exact hc
            intro heq
            apply hdiff_ne_zero
            rw [heq, sub_self]
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff_ne_zero : ((f.a * w2 + f.b) / (f.c * w2 + f.d)) - ((f.a * w1 + f.b) / (f.c * w1 + f.d)) ≠ 0 := by
              rw [apply_sub w2 w1 hp2 hp1]
              refine div_ne_zero ?_ (mul_ne_zero hp2 hp1)
              refine mul_ne_zero hdet (sub_ne_zero.mpr ?_)
              exact h12.symm
            intro heq
            apply hdiff_ne_zero
            rw [heq, sub_self]

    -- ─────────────────────────────────────────────────────────────
    -- CASE B.3: z1 = ∞, others finite
    -- ─────────────────────────────────────────────────────────────
    | EComplex.some w0, none, EComplex.some w2, EComplex.some w3 =>
      have h02 : w0 ≠ w2 := by exact_mod_cast h02
      have h03 : w0 ≠ w3 := by exact_mod_cast h03
      have h23 : w2 ≠ w3 := by exact_mod_cast h23
      have apply_inf : f none = EComplex.some (f.a / f.c) := by
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        -- congr 1

      have apply_finite : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f (EComplex.some w) = EComplex.some ((f.a * w + f.b) / (f.c * w + f.d)) := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have condiction_ne : w ≠ -f.d / f.c := by
          intro heq
          field_simp at heq
          rw[eq_neg_iff_add_eq_zero,mul_comm] at heq
          contradiction
        simp [condiction_ne]
        -- congr 1

      have apply_pole : ∀ w : ℂ, f.c * w + f.d = 0 → f (EComplex.some w) = none := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have : w = -f.d / f.c := by
          field_simp [hc] at hw
          field_simp [hc]
          rw [eq_neg_iff_add_eq_zero,mul_comm]
          exact hw
        simp [this]

      have apply_inf_sub : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f.a / f.c - (f.a * w + f.b) / (f.c * w + f.d) =
          (f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
        intro w hw
        field_simp [hc, hw]
        ring_nf

      have apply_sub : ∀ w1 w2 : ℂ, f.c * w1 + f.d ≠ 0 → f.c * w2 + f.d ≠ 0 →
          (f.a * w1 + f.b) / (f.c * w1 + f.d) - (f.a * w2 + f.b) / (f.c * w2 + f.d) =
          (f.a * f.d - f.b * f.c) * (w1 - w2) / ((f.c * w1 + f.d) * (f.c * w2 + f.d)) := by
        intro w1 w2 hw1 hw2
        rw [div_sub_div _ _ hw1 hw2]
        congr 1
        ring_nf


      by_cases hp0 : f.c * w0 + f.d = 0

      ·-- CASE B.3.a: w0 is at the pole
        have hp2 := ne_pole_of_ne_of_pole f hc w0 w2 h02 hp0 --f.ne_pole_of_ne_of_pole hc w0 w2 h02 hp0
        have hp3 := ne_pole_of_ne_of_pole f hc w0 w3 h03 hp0 --f.ne_pole_of_ne_of_pole hc w0 w3 h03 hp0
        have h_right : cross_ratio (↑w0 : ℂ∞) none (↑w2) (↑w3) = cross_ratio (Option.some  w0) none (Option.some  w2) (Option.some  w3) := by
          rfl
        have h_left : cross_ratio (f.apply ↑w0) (f.apply none) (f.apply ↑w2) (f.apply ↑w3) =
          cross_ratio (f.apply (Option.some w0)) (f.apply none) (f.apply (Option.some w2)) (f.apply (Option.some w3)) := by
          rfl
        rw [h_left]
        rw [apply_some_of_pole f hc w0 hp0, apply_none f hc,
            apply_some_of_ne_pole f hc w2 hp2,
            apply_some_of_ne_pole f hc w3 hp3]
        have h1_left : cross_ratio none (Option.some (f.a / f.c)) (Option.some ((f.a * w2 + f.b) / (f.c * w2 + f.d)))
                       (Option.some ((f.a * w3 + f.b) / (f.c * w3 + f.d))) =
                       cross_ratio none (↑(f.a / f.c)) (↑((f.a * w2 + f.b) / (f.c * w2 + f.d))) (↑((f.a * w3 + f.b) / (f.c * w3 + f.d))) := by
          rfl
        rw[h1_left]
        rw [cross_ratio_none_z1_eq, cross_ratio_none_z0_eq]
        rw [apply_sub_apply f w2 w3 hp2 hp3,
            apply_sub_apply_none f hc w2 hp2]
        have hw0 := (pole_iff f hc w0).mp hp0
        rw [hw0]
        have hdet := f.determinant_ne_zero
        have hprod23 : (f.c * w2 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp2 hp3
        field_simp [hc, hdet, hprod23]
        congr 1
        have h_denom : -f.d - f.c * w3 ≠ 0 := by
          intro hzero
          apply hp3
          calc
            f.c * w3 + f.d = -(-f.d - f.c * w3) := by ring
            _ = -0 := by rw [hzero]
            _ = 0 := neg_zero
        field_simp [hp3, h_denom, hc]
        ring_nf
        intro heq
        field_simp at heq
        rw [mul_comm] at hp2
        field_simp at heq
        ring_nf at heq
        have h_eq : f.b * f.c = f.a * f.d := by
          calc
            f.b * f.c = (f.a * w2 * f.c + f.b * f.c) - f.a * w2 * f.c := by ring_nf
            _ = (f.a * w2 * f.c + f.a * f.d) - f.a * w2 * f.c := by rw [heq]
            _ = f.a * f.d := by ring_nf
        apply f.determinant_ne_zero
        rw [h_eq]
        ring_nf
        (expose_names; exact coe_ne_coe_iff.mp h03_1)

      · by_cases hp2 : f.c * w2 + f.d = 0

        ·-- CASE B.3.b: w2 is at the pole
          rw [apply_inf, apply_pole w2 hp2]
          have hp0' : f.c * w0 + f.d ≠ 0 := hp0
          have hp3 : f.c * w3 + f.d ≠ 0 := by
            intro h
            have this1 : w3 = -f.d / f.c := by
              field_simp [hc] at h
              field_simp [hc]
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact h
            have this2 : w2 = -f.d / f.c := by
              field_simp [hc] at hp2
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact hp2
            rw [← this1] at this2
            contradiction
          rw [apply_finite w0 hp0', apply_finite w3 hp3]
          rw [cross_ratio_none_z2_eq, cross_ratio_none_z1_eq]
          have apply_sub_inf : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
              (f.a * w + f.b) / (f.c * w + f.d) - f.a / f.c =
              -(f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
            intro w hw
            field_simp [hc, hw]
            rw [mul_comm] at hw
            field_simp [hw]
            ring_nf
          rw [apply_sub_inf w0 hp0', apply_sub w0 w3 hp0' hp3]
          have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
          have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
          have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
          have hprod03 : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0' hp3

          have hw2 : w2 = -f.d / f.c := by
            field_simp [hc] at hp2
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact hp2

          field_simp [hc, hdet, hprod03]
          rw [hw2]
          congr 1
          have h_denom1 : f.c * (w0 - w3) ≠ 0 := mul_ne_zero hc hdiff03
          field_simp [h_denom1, hdiff03]
          ring_nf
          (expose_names; exact coe_ne_coe_iff.mp h03_1)
          have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
          have h_diff_ne_zero : ((f.a * w0 + f.b) / (f.c * w0 + f.d)) - ((f.a * w3 + f.b) / (f.c * w3 + f.d)) ≠ 0 := by
            rw [apply_sub w0 w3 hp0' hp3]
            refine div_ne_zero (mul_ne_zero hdet (sub_ne_zero.mpr h03)) (mul_ne_zero hp0' hp3)
          intro heq
          apply h_diff_ne_zero
          rw [heq, sub_self]

        · by_cases hp3 : f.c * w3 + f.d = 0

          ·-- CASE B.3.c: w3 is at the pole
            rw [apply_inf, apply_pole w3 hp3]
            have hp0' : f.c * w0 + f.d ≠ 0 := hp0
            have hp2' : f.c * w2 + f.d ≠ 0 := hp2

            rw [apply_finite w0 hp0', apply_finite w2 hp2']
            rw [cross_ratio_none_z3_eq, cross_ratio_none_z1_eq]

            have apply_sub_inf : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
                (f.a * w + f.b) / (f.c * w + f.d) - f.a / f.c =
                -(f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
              intro w hw
              field_simp [hc, hw]
              rw[mul_comm] at hw
              field_simp [hw]
              ring_nf

            rw [apply_sub_inf w0 hp0', apply_sub_inf w2 hp2']
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
            have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03

            have hw3 : w3 = -f.d / f.c := by
              field_simp [hc] at hp3
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact hp3

            field_simp [hc, hdet]
            rw [hw3]
            congr 1
            have h_denom_right : w0 - (-f.d / f.c) ≠ 0 := by
              intro h
              apply hp0'
              calc
                f.c * w0 + f.d = f.c * (w0 - (-f.d / f.c)) := by {
                  field_simp [hc]
                  ring_nf
                }
                _ = f.c * 0 := by rw [h]
                _ = 0 := mul_zero _
            field_simp [hp0', h_denom_right, hc]
            ring_nf
            (expose_names; exact coe_ne_coe_iff.mp h03_1)
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have h_diff_ne_zero : f.a / f.c - (f.a * w2 + f.b) / (f.c * w2 + f.d) ≠ 0 := by
              rw [apply_inf_sub w2 hp2']
              refine div_ne_zero hdet (mul_ne_zero hc hp2')
            by_contra heq
            apply h_diff_ne_zero
            rw [heq, sub_self]

          ·-- CASE B.3.d: No pole among w0, w2, w3
            rw [apply_inf, apply_finite w0 hp0, apply_finite w2 hp2, apply_finite w3 hp3]
            rw [cross_ratio_some_eq, cross_ratio_none_z1_eq]

            have apply_sub_inf : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
                (f.a * w + f.b) / (f.c * w + f.d) - f.a / f.c =
                -(f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
              intro w hw
              field_simp [hc, hw]
              rw[mul_comm] at hw
              field_simp [hw]
              ring_nf

            rw [apply_sub_inf w0 hp0, apply_sub w0 w3 hp0 hp3,
                apply_sub w2 w3 hp2 hp3, apply_sub_inf w2 hp2]

            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
            have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
            have hprod03 : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0 hp3
            have hprod23 : (f.c * w2 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp2 hp3

            field_simp [hc, hdet, hprod03, hprod23]
            (expose_names; exact coe_ne_coe_iff.mp h03_1)
            intro heq
            have hsub := apply_sub w0 w3 hp0 hp3
            rw [heq, sub_self] at hsub
            have hw : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
            have hdenom : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0 hp3
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hnum : (f.a * f.d - f.b * f.c) * (w0 - w3) ≠ 0 := mul_ne_zero hdet hw
            exact hnum (div_eq_zero_iff.mp hsub.symm |>.resolve_right hdenom)
            intro heq
            have hsub := apply_inf_sub w2 hp2
            rw [heq, sub_self] at hsub
            have hdenom : f.c * (f.c * w2 + f.d) ≠ 0 := mul_ne_zero hc hp2
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            exact hdet (div_eq_zero_iff.mp hsub.symm |>.resolve_right hdenom)


    -- ─────────────────────────────────────────────────────────────
    -- CASE B.4: z2 = ∞, others finite
    -- ─────────────────────────────────────────────────────────────
    | EComplex.some w0, EComplex.some w1, none, EComplex.some w3 =>

      have h01 : w0 ≠ w1 := by exact_mod_cast h01
      have h03 : w0 ≠ w3 := by exact_mod_cast h03
      have h13 : w1 ≠ w3 := by exact_mod_cast h13

      have apply_inf : f none = EComplex.some (f.a / f.c) := by
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        --congr 1

      have apply_finite : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f (EComplex.some w) = EComplex.some ((f.a * w + f.b) / (f.c * w + f.d)) := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have condiction_ne : w ≠ -f.d / f.c := by
          intro heq
          field_simp at heq
          rw[eq_neg_iff_add_eq_zero,mul_comm] at heq
          contradiction
        simp [condiction_ne]
        --congr 1

      have apply_pole : ∀ w : ℂ, f.c * w + f.d = 0 → f (EComplex.some w) = none := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have : w = -f.d / f.c := by
          field_simp [hc] at hw
          field_simp [hc]
          rw [eq_neg_iff_add_eq_zero,mul_comm]
          exact hw
        simp [this]
      have apply_inf_sub : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f.a / f.c - (f.a * w + f.b) / (f.c * w + f.d) =
          (f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
        intro w hw
        field_simp [hc, hw]
        ring_nf
      have apply_sub : ∀ w1 w2 : ℂ, f.c * w1 + f.d ≠ 0 → f.c * w2 + f.d ≠ 0 →
          (f.a * w1 + f.b) / (f.c * w1 + f.d) - (f.a * w2 + f.b) / (f.c * w2 + f.d) =
          (f.a * f.d - f.b * f.c) * (w1 - w2) / ((f.c * w1 + f.d) * (f.c * w2 + f.d)) := by
        intro w1 w2 hw1 hw2
        rw [div_sub_div _ _ hw1 hw2]
        congr 1
        ring_nf
      by_cases hp0 : f.c * w0 + f.d = 0
      ·-- CASE B.4.a: w0 is at the pole
        rw [apply_pole w0 hp0, apply_inf]
        have hp1 : f.c * w1 + f.d ≠ 0 := by
          intro h
          have this1 : w1 = -f.d / f.c := by
            field_simp [hc] at h
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact h
          have this2 : w0 = -f.d / f.c := by
            field_simp [hc] at hp0
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact hp0
          rw [← this1] at this2
          (expose_names; exact Ne.elim h01_1 (congrArg EComplex.some this2))
        have hp3 : f.c * w3 + f.d ≠ 0 := by
          intro h
          have this1 : w3 = -f.d / f.c := by
            field_simp [hc] at h
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact h
          have this2 : w0 = -f.d / f.c := by
            field_simp [hc] at hp0
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact hp0
          rw [← this1] at this2
          (expose_names; exact Ne.elim h03_1 (congrArg EComplex.some this2))


        rw [apply_finite w1 hp1, apply_finite w3 hp3]
        rw [cross_ratio_none_z0_eq, cross_ratio_none_z2_eq]
        rw [apply_inf_sub w3 hp3, apply_inf_sub w1 hp1]

        have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
        have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
        have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03

        have hw0 : w0 = -f.d / f.c := by
          field_simp [hc] at hp0
          field_simp
          rw [eq_neg_iff_add_eq_zero,mul_comm]
          exact hp0

        congr 1
        rw [hw0]
        field_simp [hc, hp1, hp3, hdet]
        have h : -f.d - f.c * w3 ≠ 0 := by
          have : -f.d - f.c * w3 = -(f.c * w3 + f.d) := by ring
          rw [this]
          exact neg_ne_zero.mpr hp3
        field_simp [h]
        ring_nf
        (expose_names; exact coe_ne_coe_iff.mp h03_1)
        have := apply_inf_sub w1 hp1
        have hdenom : f.c * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hc hp1
        have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
        exact sub_ne_zero.mp (by rw [this]; exact div_ne_zero hdet hdenom)


      · by_cases hp1 : f.c * w1 + f.d = 0

        ·-- CASE B.4.b: w1 is at the pole
          rw [apply_inf, apply_pole w1 hp1]
          have hp0' : f.c * w0 + f.d ≠ 0 := hp0
          have hp3 : f.c * w3 + f.d ≠ 0 := by
            intro h
            have this1 : w3 = -f.d / f.c := by
              field_simp [hc] at h
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact h
            have this2 : w1 = -f.d / f.c := by
              field_simp [hc] at hp1
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact hp1
            rw [← this1] at this2
            (expose_names; exact Ne.elim h13_1 (congrArg EComplex.some this2))
          rw [apply_finite w0 hp0', apply_finite w3 hp3]
          rw [cross_ratio_none_z1_eq, cross_ratio_none_z2_eq]
          rw [apply_inf_sub w3 hp3, apply_sub w0 w3 hp0' hp3]
          have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
          have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
          have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
          have hprod03 : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0' hp3

          have hw1 : w1 = -f.d / f.c := by
            field_simp [hc] at hp1
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact hp1
          congr 1
          rw [hw1]
          field_simp [hc, hdet, hprod03]
          ring_nf
          (expose_names; exact coe_ne_coe_iff.mp h03_1)
          have hsub := apply_sub w0 w3 hp0' hp3
          have hdenom : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0' hp3
          have hnum : (f.a * f.d - f.b * f.c) * (w0 - w3) ≠ 0 :=
            mul_ne_zero f.determinant_ne_zero (sub_ne_zero.mpr h03)
          exact sub_ne_zero.mp (by rw [hsub]; exact div_ne_zero hnum hdenom)

        · by_cases hp3 : f.c * w3 + f.d = 0

          ·-- CASE B.4.c: w3 is at the pole
            rw [apply_inf, apply_pole w3 hp3]
            have hp0' : f.c * w0 + f.d ≠ 0 := hp0
            have hp1' : f.c * w1 + f.d ≠ 0 := hp1
            rw [apply_finite w0 hp0', apply_finite w1 hp1']
            rw [cross_ratio_none_z3_eq, cross_ratio_none_z2_eq]
            rw [apply_sub w0 w1 hp0' hp1', apply_inf_sub w1 hp1']
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
            have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
            have hprod01 : (f.c * w0 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp0' hp1'
            have hw3 : w3 = -f.d / f.c := by
              field_simp [hc] at hp3
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact hp3
            congr 1
            rw [hw3]
            field_simp [hc, hdet, hprod01,hp0]
            ring_nf
            (expose_names; exact coe_ne_coe_iff.mp h03_1)
            have hsub := apply_inf_sub w1 hp1'
            have hdenom : f.c * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hc hp1'
            exact sub_ne_zero.mp (by rw [hsub]; exact div_ne_zero f.determinant_ne_zero hdenom)

          ·-- CASE B.4.d: No pole among w0, w1, w3
            rw [apply_inf, apply_finite w0 hp0, apply_finite w1 hp1, apply_finite w3 hp3]
            rw [cross_ratio_some_eq, cross_ratio_none_z2_eq]
            rw [apply_sub w0 w1 hp0 hp1, apply_sub w0 w3 hp0 hp3,
                apply_inf_sub w3 hp3, apply_inf_sub w1 hp1]
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
            have hdiff03 : w0 - w3 ≠ 0 := sub_ne_zero.mpr h03
            have hprod01 : (f.c * w0 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp0 hp1
            have hprod03 : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0 hp3
            field_simp [hc, hdet, hprod01, hprod03]
            (expose_names; exact coe_ne_coe_iff.mp h03_1)
            have hsub := apply_sub w0 w3 hp0 hp3
            have hdenom : (f.c * w0 + f.d) * (f.c * w3 + f.d) ≠ 0 := mul_ne_zero hp0 hp3
            have hnum : (f.a * f.d - f.b * f.c) * (w0 - w3) ≠ 0 :=
              mul_ne_zero f.determinant_ne_zero (sub_ne_zero.mpr h03)
            exact sub_ne_zero.mp (by rw [hsub]; exact div_ne_zero hnum hdenom)
            have hsub := apply_inf_sub w1 hp1
            have hdenom : f.c * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hc hp1
            exact sub_ne_zero.mp (by rw [hsub]; exact div_ne_zero f.determinant_ne_zero hdenom)

    -- ─────────────────────────────────────────────────────────────
    -- CASE B.5: z3 = ∞, others finite
    -- ─────────────────────────────────────────────────────────────
    | EComplex.some w0, EComplex.some w1, EComplex.some w2, none =>
      have h01 : w0 ≠ w1 := by exact_mod_cast h01
      have h02 : w0 ≠ w2 := by exact_mod_cast h02
      have h12 : w1 ≠ w2 := by exact_mod_cast h12

      have apply_inf : f none = EComplex.some (f.a / f.c) := by
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        --congr 1

      have apply_finite : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f (EComplex.some w) = EComplex.some ((f.a * w + f.b) / (f.c * w + f.d)) := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have condiction_ne : w ≠ -f.d / f.c := by
          intro heq
          field_simp at heq
          rw[eq_neg_iff_add_eq_zero,mul_comm] at heq
          contradiction
        simp [condiction_ne]
        --congr 1

      have apply_pole : ∀ w : ℂ, f.c * w + f.d = 0 → f (EComplex.some w) = none := by
        intro w hw
        simp only [LinearFracTrans.apply, hc, ↓reduceIte]
        have : w = -f.d / f.c := by
          field_simp [hc] at hw
          field_simp [hc]
          rw [eq_neg_iff_add_eq_zero,mul_comm]
          exact hw
        simp [this]

      have apply_inf_sub : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
          f.a / f.c - (f.a * w + f.b) / (f.c * w + f.d) =
          (f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
        intro w hw
        field_simp [hc, hw]
        ring_nf

      have apply_sub : ∀ w1 w2 : ℂ, f.c * w1 + f.d ≠ 0 → f.c * w2 + f.d ≠ 0 →
          (f.a * w1 + f.b) / (f.c * w1 + f.d) - (f.a * w2 + f.b) / (f.c * w2 + f.d) =
          (f.a * f.d - f.b * f.c) * (w1 - w2) / ((f.c * w1 + f.d) * (f.c * w2 + f.d)) := by
        intro w1 w2 hw1 hw2
        rw [div_sub_div _ _ hw1 hw2]
        congr 1
        ring_nf

      have apply_sub_inf : ∀ w : ℂ, f.c * w + f.d ≠ 0 →
            (f.a * w + f.b) / (f.c * w + f.d) - f.a / f.c =
            -(f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
          intro w hw
          field_simp [hc, hw]
          rw [mul_comm]
          field_simp [hw]
          ring_nf


      by_cases hp0 : f.c * w0 + f.d = 0

      ·-- CASE B.5.a: w0 is at the pole
        rw [apply_pole w0 hp0, apply_inf]
        have hp1 : f.c * w1 + f.d ≠ 0 := by
          intro h
          have this1 : w1 = -f.d / f.c := by
            field_simp [hc] at h
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact h
          have this2 : w0 = -f.d / f.c := by
            field_simp [hc] at hp0
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact hp0
          rw [← this1] at this2
          (expose_names; exact Ne.elim h01_1 (congrArg EComplex.some this2))
        have hp2 : f.c * w2 + f.d ≠ 0 := by
          intro h
          have this1 : w2 = -f.d / f.c := by
            field_simp [hc] at h
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact h
          have this2 : w0 = -f.d / f.c := by
            field_simp [hc] at hp0
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact hp0
          rw [← this1] at this2
          (expose_names; exact Ne.elim h02_1 (congrArg EComplex.some this2))
        rw [apply_finite w1 hp1, apply_finite w2 hp2]
        rw [cross_ratio_none_z0_eq, cross_ratio_none_z3_eq]
        rw [apply_sub_inf w2 hp2, apply_sub w2 w1 hp2 hp1]
        have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
        have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
        have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
        have hprod21 : (f.c * w2 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp2 hp1
        have hw0 : w0 = -f.d / f.c := by
          field_simp [hc] at hp0
          field_simp
          rw [eq_neg_iff_add_eq_zero,mul_comm]
          exact hp0
        field_simp [hc, hdet, hprod21]
        congr 1
        rw [hw0]
        field_simp [hc, hdiff21]
        ring_nf
        (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
        have hsub := apply_sub w2 w1 hp2 hp1
        have hdenom : (f.c * w2 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp2 hp1
        have hnum : (f.a * f.d - f.b * f.c) * (w2 - w1) ≠ 0 :=
          mul_ne_zero f.determinant_ne_zero (sub_ne_zero.mpr h12.symm)
        exact sub_ne_zero.mp (by rw [hsub]; exact div_ne_zero hnum hdenom)

      · by_cases hp1 : f.c * w1 + f.d = 0
        ·-- CASE B.5.b: w1 is at the pole
          rw [apply_inf, apply_pole w1 hp1]
          have hp0' : f.c * w0 + f.d ≠ 0 := hp0
          have hp2 : f.c * w2 + f.d ≠ 0 := by
            intro h
            have this1 : w2 = -f.d / f.c := by
              field_simp [hc] at h
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact h
            have this2 : w1 = -f.d / f.c := by
              field_simp [hc] at hp1
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact hp1
            rw [← this1] at this2
            (expose_names; exact Ne.elim h12_1 (congrArg EComplex.some this2))
          rw [apply_finite w0 hp0', apply_finite w2 hp2]
          rw [cross_ratio_none_z1_eq, cross_ratio_none_z3_eq]
          rw [apply_sub_inf w2 hp2, apply_sub_inf w0 hp0']
          have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
          have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
          have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
          have hw1 : w1 = -f.d / f.c := by
            field_simp [hc] at hp1
            field_simp
            rw [eq_neg_iff_add_eq_zero,mul_comm]
            exact hp1
          field_simp [hc, hdet]
          congr 1
          field_simp[h12.symm,hp2]
          rw [hw1]
          field_simp [hc]
          ring_nf
          (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
          have hsub := apply_sub_inf w0 hp0'
          have hnum : -(f.a * f.d - f.b * f.c) ≠ 0 := neg_ne_zero.mpr f.determinant_ne_zero
          have hdenom : f.c * (f.c * w0 + f.d) ≠ 0 := mul_ne_zero hc hp0'
          exact sub_ne_zero.mp (by rw [hsub]; exact div_ne_zero hnum hdenom)


        · by_cases hp2 : f.c * w2 + f.d = 0

          ·-- CASE B.5.c: w2 is at the pole
            rw [apply_inf, apply_pole w2 hp2]
            have hp0' : f.c * w0 + f.d ≠ 0 := hp0
            have hp1' : f.c * w1 + f.d ≠ 0 := hp1
            rw [apply_finite w0 hp0', apply_finite w1 hp1']
            rw [cross_ratio_none_z2_eq, cross_ratio_none_z3_eq]
            rw [apply_sub w0 w1 hp0' hp1', apply_sub_inf w0 hp0']
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
            have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
            have hprod01 : (f.c * w0 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp0' hp1'
            have hw2 : w2 = -f.d / f.c := by
              field_simp [hc] at hp2
              field_simp
              rw [eq_neg_iff_add_eq_zero,mul_comm]
              exact hp2
            congr 1
            field_simp [hc, hdet, hprod01]
            rw [hw2]
            field_simp [hc]
            ring_nf
            (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
            have hsub := apply_sub_inf w0 hp0'
            have hnum : -(f.a * f.d - f.b * f.c) ≠ 0 := neg_ne_zero.mpr f.determinant_ne_zero
            have hdenom : f.c * (f.c * w0 + f.d) ≠ 0 := mul_ne_zero hc hp0'
            exact sub_ne_zero.mp (by rw [hsub]; exact div_ne_zero hnum hdenom)
          ·-- CASE B.5.d: No pole among w0, w1, w2
            rw [apply_inf, apply_finite w0 hp0, apply_finite w1 hp1, apply_finite w2 hp2]
            rw [cross_ratio_some_eq, cross_ratio_none_z3_eq]
            rw [apply_sub w0 w1 hp0 hp1, apply_sub_inf w0 hp0,
                apply_sub_inf w2 hp2, apply_sub w2 w1 hp2 hp1]
            have hdet : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
            have hdiff01 : w0 - w1 ≠ 0 := sub_ne_zero.mpr h01
            have hdiff21 : w2 - w1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr h12)
            have hprod01 : (f.c * w0 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp0 hp1
            have hprod21 : (f.c * w2 + f.d) * (f.c * w1 + f.d) ≠ 0 := mul_ne_zero hp2 hp1
            congr 1
            field_simp [hc, hdet, hprod01, hprod21]
            (expose_names; exact coe_ne_coe_iff.mp (id (Ne.symm h12_1)))
            rw [ne_eq, ← sub_eq_zero, apply_sub_inf w0 hp0]
            apply div_ne_zero
            · exact neg_ne_zero.mpr f.determinant_ne_zero
            · exact mul_ne_zero hc hp0
            rw [ne_eq, ← sub_eq_zero, apply_sub w2 w1 hp2 hp1]
            apply div_ne_zero
            · apply mul_ne_zero
              · exact f.determinant_ne_zero
              · exact sub_ne_zero.mpr h12.symm
            · exact mul_ne_zero hp2 hp1
    -- ─────────────────────────────────────────────────────────────
    -- IMPOSSIBLE CASES: Two or more points are ∞
    -- These contradict distinctness
    -- ─────────────────────────────────────────────────────────────
    | none, none, _, _ => exact absurd rfl h01
    | none, _, none, _ => exact absurd rfl h02
    | none, _, _, none => exact absurd rfl h03
    | _, none, none, _ => exact absurd rfl h12
    | _, none, _, none => exact absurd rfl h13
    | _, _, none, none => exact absurd rfl h23




/--  #### Lemma (Swap 2nd and 4th arguments)
  Swapping the second and fourth arguments of the cross
  ratio yields the multiplicative inverse.
-/
lemma cross_ratio_swap_13_inv (z0 z1 z2 z3 : EComplex)
    (h_distinct : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) :
    cross_ratio z0 z3 z2 z1 = 1 / cross_ratio z0 z1 z2 z3 := by
  -- Extract distinctness facts we'll need
  -- h01 : z0 ≠ z1, h02 : z0 ≠ z2, h03 : z0 ≠ z3
  -- h12 : z1 ≠ z2, h13 : z1 ≠ z3, h23 : z2 ≠ z3
  have h01 : z0 ≠ z1 := by exact pairwise_distinct_0_1 h_distinct
  have h02 : z0 ≠ z2 := by exact pairwise_distinct_0_2 h_distinct
  have h03 : z0 ≠ z3 := by exact pairwise_distinct_0_3 h_distinct
  have h12 : z1 ≠ z2 := by exact pairwise_distinct_1_2 h_distinct
  have h13 : z1 ≠ z3 := by exact pairwise_distinct_1_3 h_distinct
  have h23 : z2 ≠ z3 := by exact pairwise_distinct_2_3 h_distinct
  -- Case split on which point is infinity
  cases z0 with
  | none =>
    -- z0 = ∞
    cases z1 with
    | none => contradiction
    | some b =>
      cases z2 with
      | none => contradiction
      | some c =>
        cases z3 with
        | none => contradiction
        | some d =>
          -- Case: z0 = ∞, z1 = some b, z2 = some c, z3 = some d
          have hbc : b ≠ c := by
            intro heq
            apply h12
            rw [heq]
          -- Extract c ≠ d from h23 : some c ≠ some d
          have hcd : c ≠ d := by
            intro heq
            apply h23
            rw [heq]
          -- Get the nonzero differences
          have hcb : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
          have hdc : c - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd.symm)
          -- Unfold cross_ratio and simplify
          simp only [cross_ratio]
          rw [@sub_some c b, @sub_some c d]
          rw [@one_div_div (c - d) (c - b) hdc hcb]
  | some a =>
    cases z1 with
    | none =>
      -- z1 = ∞
      cases z2 with
      | none => contradiction
      | some c =>
        cases z3 with
        | none => contradiction
        | some d =>
          -- Case: z0 = some a, z1 = ∞, z2 = some c, z3 = some d
          -- Extract a ≠ d from h03 : some a ≠ some d
          have had : a ≠ d := by
            intro heq
            apply h03
            rw [heq]
          -- Extract c ≠ d from h23 : some c ≠ some d
          have hcd : c ≠ d := by
            intro heq
            apply h23
            rw [heq]
          -- Get the nonzero differences
          have had' : a - d ≠ 0 := sub_ne_zero.mpr had
          have hcd' : c - d ≠ 0 := sub_ne_zero.mpr hcd
         -- Unfold cross_ratio and simplify
          simp only [cross_ratio]
          have typechangea : Option.some a = EComplex.some a := rfl
          rw [typechangea]
          rw [@sub_some a d, @sub_some c d]
          rw [@one_div_div (c - d) (a - d) hcd' had']
    | some b =>
      cases z2 with
      | none =>
        -- z2 = ∞
        cases z3 with
        | none => contradiction
        | some d =>
          -- Case: z0 = some a, z1 = some b, z2 = ∞, z3 = some d
          have hab : a ≠ b := by
            intro heq
            apply h01
            rw [heq]
         -- Extract a ≠ d from h03 : some a ≠ some d
          have had : a ≠ d := by
            intro heq
            apply h03
            rw [heq]
        -- Get the nonzero differences
          have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
          have had' : a - d ≠ 0 := sub_ne_zero.mpr had
        -- Unfold cross_ratio and simplify
          simp only [cross_ratio]
          have typechangea : Option.some a = EComplex.some a := rfl
          rw [typechangea]
          rw [@sub_some a d, @sub_some a b]
          rw [@one_div_div (a - b) (a - d) hab' had']
      | some c =>
        cases z3 with
        | none =>
          -- Case: z0 = some a, z1 = some b, z2 = some c, z3 = ∞
          have hab : a ≠ b := by
            intro heq
            apply h01
            rw [heq]
          -- Extract b ≠ c from h12 : some b ≠ some c
          have hbc : b ≠ c := by
            intro heq
            apply h12
            rw [heq]
          -- Get the nonzero differences
          have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
          have hcb' : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
          -- Unfold cross_ratio and simplify
          simp only [cross_ratio]
          have typechangea : Option.some a = EComplex.some a := rfl
          rw [typechangea]
          rw [@sub_some c b, @sub_some a b]
          rw [@one_div_div (a - b) (c - b) hab' hcb']
        | some d =>
          -- Case: all finite (main case)
          -- z0 = some a, z1 = some b, z2 = some c, z3 = some d
          -- Case: z0 = some a, z1 = some b, z2 = some c, z3 = some d (all finite)
          -- Extract distinctness
          have hab : a ≠ b := by
            intro heq
            apply h01
            rw [heq]
          have hac : a ≠ c := by
            intro heq
            apply h02
            rw [heq]
          have had : a ≠ d := by
            intro heq
            apply h03
            rw [heq]
          have hbc : b ≠ c := by
            intro heq
            apply h12
            rw [heq]
          have hbd : b ≠ d := by
            intro heq
            apply h13
            rw [heq]
          have hcd : c ≠ d := by
            intro heq
            apply h23
            rw [heq]
          -- Get nonzero differences
          have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
          have had' : a - d ≠ 0 := sub_ne_zero.mpr had
          have hcb' : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
          have hcd' : c - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd.symm)
          -- Unfold cross_ratio
          simp only [cross_ratio]
          -- Rewrite using sub_some
          rw [@sub_some a d, @sub_some a b, @sub_some c b, @sub_some c d]
          -- Use div_mul_div to combine fractions
          rw [@div_mul_div (a - d) (a - b) (c - b) (c - d) hab' hcd']
          rw [@div_mul_div (a - b) (a - d) (c - d) (c - b) had' hcb']
          -- Now we have: some X / some Y = 1 / (some Y / some X)
          -- where X = (a-d)*(c-b) and Y = (a-b)*(c-d)
          have hX : (a - d) * (c - b) ≠ 0 := mul_ne_zero had' hcb'
          have hY : (a - b) * (c - d) ≠ 0 := mul_ne_zero hab' hcd'
          rw [@one_div_div ((a - b) * (c - d)) ((a - d) * (c - b)) hY hX]


/--
  #### Lemma (Swap 2nd and 3rd arguments)
Swapping the second and third
arguments of the cross ratio yields the additive complement.
That is, if λ = (z0, z1; z2, z3),
then (z0, z2; z1, z3) = 1 − λ.
This is the second of two generators needed to produce
all six values of the cross ratio under permutation.
-/
lemma cross_ratio_swap_12_complement (z0 z1 z2 z3 : EComplex)
    (h_distinct : List.Pairwise (· ≠ ·) [z0, z1, z2, z3]) :
    cross_ratio z0 z2 z1 z3 = 1 - cross_ratio z0 z1 z2 z3 := by
  -- Extract distinctness facts
  have h01 : z0 ≠ z1 := by exact pairwise_distinct_0_1 h_distinct
  have h02 : z0 ≠ z2 := by exact pairwise_distinct_0_2 h_distinct
  have h03 : z0 ≠ z3 := by exact pairwise_distinct_0_3 h_distinct
  have h12 : z1 ≠ z2 := by exact pairwise_distinct_1_2 h_distinct
  have h13 : z1 ≠ z3 := by exact pairwise_distinct_1_3 h_distinct
  have h23 : z2 ≠ z3 := by exact pairwise_distinct_2_3 h_distinct
  -- Case split on which point is infinity
  cases z0 with
  | none =>
    -- z0 = ∞
    cases z1 with
    | none => contradiction
    | some b =>
      cases z2 with
      | none => contradiction
      | some c =>
        cases z3 with
        | none => contradiction
        | some d =>
          -- Case 1: z0 = ∞, z1 = some b, z2 = some c, z3 = some d
          have hbc : b ≠ c := by
            intro heq
            apply h12
            rw [heq]
          have hcd : c ≠ d := by
            intro heq
            apply h23
            rw [heq]
          have hbd : b ≠ d := by
            intro heq
            apply h13
            rw [heq]
          have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
          have hcb' : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
          simp only [cross_ratio]
          rw [@sub_some b d, @sub_some b c, @sub_some c d, @sub_some c b]
          rw [@one_sub_div (c - d) (c - b) hcb']
          have hnum : (c - b) - (c - d) = -(b - d) := by ring
          have hden : c - b = -(b - c) := by ring
          rw [hnum, hden]
          rw [@neg_div_neg (b - d) (b - c) hbc']

  | some a =>
    cases z1 with
    | none =>
      -- z1 = ∞
      cases z2 with
      | none => contradiction
      | some c =>
        cases z3 with
        | none => contradiction
        | some d =>
          -- Case 2: z0 = some a, z1 = ∞, z2 = some c, z3 = some d
          have hac : a ≠ c := by
            intro heq
            apply h02
            rw [heq]
          have had : a ≠ d := by
            intro heq
            apply h03
            rw [heq]
          have hcd : c ≠ d := by
            intro heq
            apply h23
            rw [heq]
          have had' : a - d ≠ 0 := sub_ne_zero.mpr had
          simp only [cross_ratio]
          have typechangea : Option.some a = EComplex.some a := rfl
          rw [typechangea]
          rw [@sub_some a c, @sub_some a d, @sub_some c d]
          rw [@one_sub_div (c - d) (a - d) had']
          -- Goal: some (a - c) / some (a - d) = some ((a - d) - (c - d)) / some (a - d)
          -- Simplify numerator: (a - d) - (c - d) = a - c
          have hnum : (a - d) - (c - d) = a - c := by ring
          rw [hnum]
    | some b =>
      cases z2 with
      | none =>
        -- z2 = ∞
        cases z3 with
        | none => contradiction
        | some d =>
          -- Case 3: z0 = some a, z1 = some b, z2 = ∞, z3 = some d
          have hab : a ≠ b := by
            intro heq
            apply h01
            rw [heq]
          have had : a ≠ d := by
            intro heq
            apply h03
            rw [heq]
          have hbd : b ≠ d := by
            intro heq
            apply h13
            rw [heq]
          have had' : a - d ≠ 0 := sub_ne_zero.mpr had
          simp only [cross_ratio]
          have typechangea : Option.some a = EComplex.some a := rfl
          rw [typechangea]
          rw [@sub_some b d, @sub_some a d, @sub_some a b]
          rw [@one_sub_div (a - b) (a - d) had']
          have hnum : (a - d) - (a - b) = b - d := by ring
          rw [hnum]
      | some c =>
        cases z3 with
        | none =>
          -- Case 4: z0 = some a, z1 = some b, z2 = some c, z3 = ∞
          have hab : a ≠ b := by
            intro heq
            apply h01
            rw [heq]
          have hac : a ≠ c := by
            intro heq
            apply h02
            rw [heq]
          have hbc : b ≠ c := by
            intro heq
            apply h12
            rw [heq]
          have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
          have hcb' : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
          simp only [cross_ratio]
          have typechangea : Option.some a = EComplex.some a := rfl
          rw [typechangea]
          rw [@sub_some a c, @sub_some b c, @sub_some a b, @sub_some c b]
          rw [@one_sub_div (a - b) (c - b) hcb']
          have hnum : (c - b) - (a - b) = -(a - c) := by ring
          have hden : c - b = -(b - c) := by ring
          rw [hnum, hden]
          rw [@neg_div_neg (a - c) (b - c) hbc']
        | some d =>
          -- Case 5: all finite (main case)
          have hab : a ≠ b := by
            intro heq
            apply h01
            rw [heq]
          have hac : a ≠ c := by
            intro heq
            apply h02
            rw [heq]
          have had : a ≠ d := by
            intro heq
            apply h03
            rw [heq]
          have hbc : b ≠ c := by
            intro heq
            apply h12
            rw [heq]
          have hbd : b ≠ d := by
            intro heq
            apply h13
            rw [heq]
          have hcd : c ≠ d := by
            intro heq
            apply h23
            rw [heq]
          have had' : a - d ≠ 0 := sub_ne_zero.mpr had
          have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
          have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
          have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
          have hcb' : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
          have hbd' : b - d ≠ 0 := sub_ne_zero.mpr hbd
          have hcd' : c - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd.symm)
          simp only [cross_ratio]
          rw [@sub_some a c, @sub_some a d, @sub_some b d, @sub_some b c]
          rw [@sub_some a b, @sub_some c d, @sub_some c b]
          rw [@div_mul_div (a - c) (a - d) (b - d) (b - c) had' hbc']
          rw [one_sub_mul_div_div (a - b) (a - d) (c - d) (c - b) had' hcb']
          have hnum : (a - d) * (c - b) - (a - b) * (c - d) = (a - c) * (d - b) := by ring
          have hnum' : (a - c) * (d - b) = -((a - c) * (b - d)) := by ring
          have hden : (a - d) * (c - b) = -((a - d) * (b - c)) := by ring
          rw [hnum, hnum', hden]
          have hprod1 : (a - d) * (b - c) ≠ 0 := mul_ne_zero had' hbc'
          have hprod2 : (a - c) * (b - d) ≠ 0 := mul_ne_zero hac' hbd'
          rw [@neg_div_neg ((a - c) * (b - d)) ((a - d) * (b - c)) hprod1]

end CrossRatio
