import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
/-! ## Convergent sequences
  This file formalizes Chapter 3 on complex sequences
  and series.
-/

open Filter Topology
open Complex

namespace ComplexSequence

/-! ## Convergence of a complex sequence -/

/-- A real sequence `x` *converges* to `a : ℝ`
  if for every `ε > 0` there is an `N` such that
  `|z n - w| < ε` for all `n ≥ N`.
 -/
def ConvergesToReal (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - a| < ε

/--
  A sequence `x` is *convergent* if there exists a limit
  `a` such that `x` converges to `a`.
-/
def isConvergentReal (x : ℕ → ℝ) : Prop :=
 ∃ a:ℝ, ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - a| < ε

def isDivergentReal (x : ℕ → ℝ) : Prop :=
  ¬ isConvergentReal x


/--  #### Definition 3.1.1

A complex sequence `z` *converges* to `w : ℂ` if
  for every `ε > 0` there is an `N` such that
  `‖z n - w‖ < ε` for all `n ≥ N`.
-/
def ConvergesTo (z : ℕ → ℂ) (w : ℂ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖z n - w‖ < ε

def isConvergent (x : ℕ → ℂ) : Prop :=
 ∃ a:ℂ , ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖x n - a‖  < ε

def isDivergent (z : ℕ → ℂ) : Prop := ¬ isConvergent z





/--
**Mathlib equivalent.** The elementary definition
of convergence of a complex sequence agrees with
`Filter.Tendsto` to the neighbourhood filter.
-/
theorem convergesToReal_iff_tendsto (x : ℕ → ℝ) (a : ℝ) :
    ConvergesToReal x a ↔ Filter.Tendsto x atTop (𝓝 a)
  := by
  simp only [ConvergesToReal, gt_iff_lt, ge_iff_le,
    Metric.tendsto_atTop]
  rfl

theorem convergesTo_iff_tendsto (z : ℕ → ℂ) (w : ℂ) :
    ConvergesTo z w ↔ Filter.Tendsto z atTop (𝓝 w) := by
  simp only [ConvergesTo, Metric.tendsto_atTop,
    dist_eq_norm]





/-! ## Reduction to real and imaginary parts -/

/-- helper lemma
If the Euclidean norm of the difference of two
complex numbers `u` and `v`, written explicitly as

`Real.sqrt ((u - v).re * (u - v).re + (u - v).im
  * (u - v).im)`

is less than `ε`, then the absolute value of the
difference of their real parts is also less than `ε`.

This is the elementary estimate
`|u.re - v.re| ≤ ‖u - v‖`.
-/
lemma abs_re_sub_lt_of_sqrt_normSq_sub_lt
    (u v : ℂ) {ε : ℝ}
    (h : Real.sqrt ((u - v).re * (u - v).re +
                  (u - v).im * (u - v).im) < ε) :
    |u.re - v.re| < ε := by
  have h_sq :
      (u.re - v.re) ^ 2 ≤ Complex.normSq (u - v) := by
    rw [← Complex.sub_re u v, pow_two]
    exact Complex.re_sq_le_normSq (u - v)
  have h_abs :
      |u.re - v.re| ≤
        Real.sqrt ((u - v).re * (u - v).re +
                   (u - v).im * (u - v).im) := by
    simpa [Complex.normSq_apply]
      using Real.abs_le_sqrt h_sq
  exact lt_of_le_of_lt h_abs h


/--
 Helper lemma analogous to the previous lemma
 with real part replaced by imaginary part.
This is the elementary estimate
`|u.im - v.im| ≤ ‖u - v‖`.
-/
lemma abs_im_sub_lt_of_sqrt_normSq_sub_lt
    (u v : ℂ) {ε : ℝ}
    (h : Real.sqrt ((u - v).re * (u - v).re +
                    (u - v).im * (u - v).im) < ε) :
    |u.im - v.im| < ε := by
  have h_sq : (u.im - v.im) ^ 2 ≤ Complex.normSq (u - v) := by
    rw [← Complex.sub_im u v, pow_two]
    exact Complex.im_sq_le_normSq (u - v)

  have h_abs :
      |u.im - v.im| ≤
        Real.sqrt ((u - v).re * (u - v).re +
                   (u - v).im * (u - v).im) := by
    simpa [Complex.normSq_apply] using Real.abs_le_sqrt h_sq

  exact lt_of_le_of_lt h_abs h


/--
If the real and imaginary parts of two complex numbers
 `u` and `v` are each within `ε / 2`, then the Euclidean
 norm of `u - v`, written explicitly using real and
 imaginary parts, is less than `ε`.

This is the estimate

`|u.re - v.re| < ε / 2` and `|u.im - v.im| < ε / 2`

imply

`√((u - v).re^2 + (u - v).im^2) < ε`.

It is useful in the proof that convergence of the
real and imaginary parts implies convergence of
the complex sequence.
-/
lemma sqrt_normSq_sub_lt_of_abs_re_im_sub_lt_half
    (u v : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hre : |u.re - v.re| < ε / 2)
    (him : |u.im - v.im| < ε / 2) :
    Real.sqrt ((u - v).re * (u - v).re +
               (u - v).im * (u - v).im) < ε := by
  rw [Real.sqrt_lt' hε]
  rw [Complex.sub_re, Complex.sub_im]

  have h_re_lt := abs_lt.mp hre
  have h_im_lt := abs_lt.mp him

  nlinarith [h_re_lt.1, h_re_lt.2, h_im_lt.1, h_im_lt.2]


/-
A complex sequence `(z_n)` converges if and only if both
`(Re z_n)` and `(Im z_n)` converge.

`w`: `z_n → w` iff `Re z_n → Re w` and `Im z_n → Im w`.
-/
theorem convergesTo_iff_re_im (z : ℕ → ℂ) (w : ℂ) :
    ConvergesTo z w ↔
      ConvergesToReal (fun n => (z n).re) w.re ∧
      ConvergesToReal (fun n => (z n).im) w.im := by

  simp only [ConvergesTo, ConvergesToReal, Complex.norm_def,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im]

  constructor
  · -- Forward direction: Convergence of `z` implies
    -- convergence of its real and imaginary parts
    intro h_conv
    constructor

    · -- Prove the real part converges
      intro ε hε
      -- Since `z` converges, there is some threshold N
      -- where the distance is < ε
      obtain ⟨N, hN⟩ := h_conv ε hε
      use N
      intro n hn

      exact abs_re_sub_lt_of_sqrt_normSq_sub_lt (z n) w
        (by simpa [Complex.sub_re, Complex.sub_im]
          using hN n hn)

    · -- Prove the imaginary part converges
      intro ε hε
      obtain ⟨N, hN⟩ := h_conv ε hε
      use N
      intro n hn

      exact abs_im_sub_lt_of_sqrt_normSq_sub_lt (z n) w
        (by simpa [Complex.sub_re, Complex.sub_im]
          using hN n hn)

  · -- Backward direction: Convergence of real and
    -- imaginary parts implies convergence of `z`
    intro h_re_im
    obtain ⟨h_re, h_im⟩ := h_re_im

    intro ε hε
    have hε_half : ε / 2 > 0 := half_pos hε

    obtain ⟨N₁, hN₁⟩ := h_re (ε / 2) hε_half
    obtain ⟨N₂, hN₂⟩ := h_im (ε / 2) hε_half

    use max N₁ N₂
    intro n hn

    have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
    have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn

    exact sqrt_normSq_sub_lt_of_abs_re_im_sub_lt_half
      (z n) w hε (hN₁ n hn₁) (hN₂ n hn₂)


/-  #### Theorem 3.1.2
  A complex sequence converges (to some limit) iff both
  its real and imaginary parts converge (to some limits).
-/
theorem exists_convergesTo_iff_re_im (z : ℕ → ℂ) :
    (∃ w, ConvergesTo z w) ↔
      (∃ a, ConvergesToReal (fun n => (z n).re) a) ∧
      (∃ b, ConvergesToReal (fun n => (z n).im) b) := by
  -- Split the "if and only if" into forward and backward
  constructor

  · -- Forward direction: If the complex sequence converges,
    -- its real and imaginary parts converge
    intro h_conv
    -- Extract the complex limit `w` and the proof that
    -- `z` converges to `w`
    obtain ⟨w, hw⟩ := h_conv

    -- Use the previous theorem to split the complex
    -- convergence into real and imaginary convergence
    have h_parts : ConvergesToReal (fun n => (z n).re) w.re ∧
                   ConvergesToReal (fun n => (z n).im) w.im :=
      (convergesTo_iff_re_im z w).mp hw

    -- Split the AND statement into two separate hypotheses
    obtain ⟨h_re, h_im⟩ := h_parts
    constructor
    · -- Prove the real part converges
      -- use w.re as the witness `a`
      use w.re
    · -- Prove the imaginary part converges
      -- use w.im as the witness `b`
      use w.im

  · -- Backward direction: If both parts converge,
    -- the complex sequence converges
    intro h_parts
    -- Extract the existence statements for both the real
    -- and imaginary parts
    obtain ⟨h_exists_re, h_exists_im⟩ := h_parts

    -- Unpack the limits `a` and `b`, along with their
    -- convergence proofs
    obtain ⟨a, ha⟩ := h_exists_re
    obtain ⟨b, hb⟩ := h_exists_im

    -- To prove the complex sequence converges, we
    -- construct the complex limit, using `a` as the real
    -- part and `b` as the imaginary part.
    let w : ℂ := Complex.mk a b
    use w

    -- Apply the backward direction of the previous theorem
    apply (convergesTo_iff_re_im z w).mpr

    -- We now need to show the real part goes to w.re and
    -- imaginary to w.im.  Since w = Complex.mk a b, w.re
    -- is exactly a, and w.im is exactly b.
    constructor
    · exact ha
    · exact hb


/--
**Mathlib equivalent.** `Tendsto` of a complex sequence is
equivalent to `Tendsto` of its real and imaginary parts.
-/
theorem tendsto_iff_re_im (z : ℕ → ℂ) (w : ℂ) :
    Filter.Tendsto z atTop (𝓝 w) ↔
    Filter.Tendsto (fun n => (z n).re) atTop (𝓝 w.re) ∧
    Filter.Tendsto (fun n => (z n).im) atTop (𝓝 w.im)
  := by
  refine ⟨ fun h => ⟨ ?_, ?_ ⟩, fun h => ?_ ⟩
  · exact Tendsto.comp ( continuous_re.tendsto _ ) h
  · exact Tendsto.comp ( continuous_im.tendsto _ ) h
  · convert continuous_ofReal.continuousAt.tendsto.comp h.1
     |> Tendsto.add <|
     continuous_ofReal.continuousAt.tendsto.comp h.2
     |> Tendsto.mul_const Complex.I using 2;
        all_goals simp







/-! ## Cauchy sequences and completeness -/

/-- A complex sequence `z` is a *Cauchy sequence*
if for every `ε > 0` there is an `N` such that
`‖z m - z n‖ < ε` whenever `m, n ≥ N`.
-/
def IsCauchy (z : ℕ → ℂ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖z m - z n‖ < ε


/-- ####  Theorem 3.1.4
A complex sequence is Cauchy iff its real and imaginary parts
are Cauchy.
-/
theorem isCauchy_iff_re_im (z : ℕ → ℂ) :
    IsCauchy z ↔
      (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        |(z m).re - (z n).re| < ε) ∧
      (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        |(z m).im - (z n).im| < ε) := by
  refine ⟨fun h => ?_, fun h => ?_⟩

  · -- Forward direction
    constructor

    · -- Real parts are Cauchy
      intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      use N
      intro m hm n hn

      have h_bound :
        Real.sqrt ((z m - z n).re * (z m - z n).re +
          (z m - z n).im * (z m - z n).im) < ε := by
        simpa [Complex.norm_def, Complex.normSq_apply]
           using hN m hm n hn

      exact abs_re_sub_lt_of_sqrt_normSq_sub_lt
        (z m) (z n) h_bound

    · -- Imaginary parts are Cauchy
      intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      use N
      intro m hm n hn

      have h_bound :
          Real.sqrt ((z m - z n).re * (z m - z n).re +
            (z m - z n).im * (z m - z n).im) < ε := by
        simpa [Complex.norm_def, Complex.normSq_apply]
          using hN m hm n hn

      exact abs_im_sub_lt_of_sqrt_normSq_sub_lt
        (z m) (z n) h_bound

  · -- Backward direction
    obtain ⟨h_re, h_im⟩ := h

    intro ε hε
    have hε_half : 0 < ε / 2 := half_pos hε

    obtain ⟨N₁, hN₁⟩ := h_re (ε / 2) hε_half
    obtain ⟨N₂, hN₂⟩ := h_im (ε / 2) hε_half

    use max N₁ N₂
    intro m hm n hn

    have hm₁ : N₁ ≤ m := le_trans (le_max_left N₁ N₂) hm
    have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
    have hm₂ : N₂ ≤ m := le_trans (le_max_right N₁ N₂) hm
    have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn

    have h_re_bound :
        |(z m).re - (z n).re| < ε / 2 :=
      hN₁ m hm₁ n hn₁

    have h_im_bound :
        |(z m).im - (z n).im| < ε / 2 :=
      hN₂ m hm₂ n hn₂

    simpa [Complex.norm_def, Complex.normSq_apply] using
      sqrt_normSq_sub_lt_of_abs_re_im_sub_lt_half
        (z m) (z n) hε h_re_bound h_im_bound




/--
A real sequence which is Cauchy in the elementary
epsilon definition is convergent.

This is where we use Mathlib's completeness theorem for `ℝ`.
The relevant Mathlib API is

* `Metric.cauchySeq_iff`, which translates the elementary
  epsilon Cauchy condition into Mathlib's `CauchySeq`;
* `cauchySeq_tendsto_of_complete`, which says that a
  Cauchy sequence in a complete space converges.
-/
lemma real_convergent_of_cauchy
    (x : ℕ → ℝ)
    (hx : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      |x m - x n| < ε) :
    ∃ a, ConvergesToReal x a := by

  -- First translate the elementary Cauchy condition
  -- into Mathlib's `CauchySeq`.
  have hx_cauchySeq : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε

    obtain ⟨N, hN⟩ := hx ε hε
    use N

    intro m hm n hn

    -- Mathlib writes the Cauchy condition using `dist`.
    -- On `ℝ`, `dist u v = |u - v|`.
    simpa [Real.dist_eq] using hN m hm n hn

  -- Since `ℝ` is complete, the Cauchy sequence converges.
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hx_cauchySeq

  -- Translate Mathlib's `Filter.Tendsto` statement back
  -- to the elementary convergence definition.
  use a
  exact (convergesToReal_iff_tendsto x a).mpr ha


/--
#### Theorem 3.1.5

The complex field is complete: every Cauchy complex sequence
converges.
-/
theorem complex_complete
    (z : ℕ → ℂ) :
    IsCauchy z → isConvergent z := by

  intro hz

  -- Use the theorem just proved: a complex sequence is
  -- Cauchy iff its real and imaginary parts are Cauchy.
  obtain ⟨h_re_cauchy, h_im_cauchy⟩
    := (isCauchy_iff_re_im z).mp hz

  -- Apply completeness of `ℝ` to
  -- the sequence of real parts
  obtain ⟨a, ha⟩ :=
    real_convergent_of_cauchy
      (fun n => (z n).re) h_re_cauchy

  -- Apply completeness of `ℝ` to
  -- the sequence of imaginary parts.
  obtain ⟨b, hb⟩ :=
    real_convergent_of_cauchy
      (fun n => (z n).im) h_im_cauchy

  -- Combine the two real limits into the complex limit
  -- change the goal to ∃ w, ConvergesTo z w
  change ∃ w, ConvergesTo z w

  apply (exists_convergesTo_iff_re_im z).mpr
  constructor
  · use a
  · use b



/--
**Mathlib equivalent.** `ℂ` is complete: a complex sequence
has a `Tendsto` limit iff it is a `CauchySeq`.
-/
theorem exists_tendsto_iff_cauchySeq (z : ℕ → ℂ) :
  (∃ w, Filter.Tendsto z atTop (𝓝 w)) ↔ CauchySeq z := by
  exact ⟨ fun ⟨ w, hw ⟩ => hw.cauchySeq, fun h =>
    cauchySeq_tendsto_of_complete h ⟩



/-! ## Convergence to the point at infinity -/

/--  #### Definition 3.1.7
A complex sequence `z` *converges to the point at
infinity* if for every `r > 0` there is an `N` such that
 `‖z k‖ > r` for all `k ≥ N`.
 -/
def ConvergesToInfinity (z : ℕ → ℂ) : Prop :=
  ∀ r > 0, ∃ N, ∀ k ≥ N, r < ‖z k‖


/-  #### Theorem 3.1.8
There is an equivalent deifnitions of convergence
to infinity.
Convergence to the point at infinity
is the statement that the norms tend to infinity
-/
/--
The real sequence of norms `‖z k‖` tends to infinity,
written without filters.

This means that for every real lower bound `b`, eventually
all the norms `‖z k‖` are at least `b`.
-/
def NormTendsToInfinity (z : ℕ → ℂ) : Prop :=
  ∀ b : ℝ, ∃ N : ℕ, ∀ k ≥ N, b ≤ ‖z k‖



/--  #### Theorem 3.1.6 a
If `z n → α` and `w n → β`, then
`a * z n + b * w n → a * α + b * β`.
-/
theorem convergesTo_linear_combination
    (z w : ℕ → ℂ) (α β a b : ℂ)
    (hz : ConvergesTo z α)
    (hw : ConvergesTo w β) :
    ConvergesTo (fun n => a * z n + b * w n)
      (a * α + b * β) := by
  sorry


/-- #### Theorem 3.1.6 b
If `z n → α` and `w n → β`, then
`z n * w n → α * β`.
-/
theorem convergesTo_mul
    (z w : ℕ → ℂ) (α β : ℂ)
    (hz : ConvergesTo z α)
    (hw : ConvergesTo w β) :
    ConvergesTo (fun n => z n * w n) (α * β) := by
  sorry


/-- #### Theorem 3.1.6 c
If `z n → α`, `w n → β`, and `β ≠ 0`, then
`z n / w n → α / β`.
-/
theorem convergesTo_div
    (z w : ℕ → ℂ) (α β : ℂ)
    (hz : ConvergesTo z α)
    (hw : ConvergesTo w β)
    (hβ : β ≠ 0) :
    ConvergesTo (fun n => z n / w n) (α / β) := by
  sorry


/-- #### Theorem 3.1.6 d
If `z n → α`, then `‖z n‖ → ‖α‖`.

This is the sequence version of

`lim |z_n| = |α|`.
-/
theorem convergesTo_norm
    (z : ℕ → ℂ) (α : ℂ)
    (hz : ConvergesTo z α) :
    ConvergesToReal (fun n => ‖z n‖) ‖α‖ := by
  sorry


/--  #### Theorem 3.1.6 e
If `z n → α`, then the conjugate sequence converges to
the conjugate limit:

`star (z n) → star α`.
-/
theorem convergesTo_conj
    (z : ℕ → ℂ) (α : ℂ)
    (hz : ConvergesTo z α) :
    ConvergesTo (fun n => star (z n)) (star α) := by
  sorry



/--
Convergence of a complex sequence to infinity is equivalent
to saying that the real sequence of norms tends to infinity
-/
theorem convergesToInfinity_iff_normTendsToInfinity
    (z : ℕ → ℂ) :
  ConvergesToInfinity z ↔ NormTendsToInfinity z := by

  constructor

  · -- Forward direction:
    -- Assume `z` converges to infinity in the complex sense.
    intro hz b

    -- We prove that the norm sequence is eventually above
    -- every real number `b`.

    -- The definition `ConvergesToInfinity` only allows
    -- us to use positive radii.  But `b` may be negative.
    --
    -- So we use the positive radius `max b 1`.
    have h_radius_pos : 0 < max b 1 := by
      have h_one_le_max : (1 : ℝ) ≤ max b 1 := by
        exact le_max_right b 1
      exact lt_of_lt_of_le zero_lt_one h_one_le_max

    -- Since `z` converges to infinity, eventually
    -- `max b 1 < ‖z k‖`.
    obtain ⟨N, hN⟩ := hz (max b 1) h_radius_pos

    -- The same `N` works for the lower bound `b`.
    use N

    intro k hk

    -- First, `b ≤ max b 1`.
    have hb_le_radius : b ≤ max b 1 := by
      exact le_max_left b 1

    -- Second, by the choice of `N`, we have
    -- `max b 1 < ‖z k‖`.
    have h_radius_lt_norm : max b 1 < ‖z k‖ := by
      exact hN k hk

    -- Therefore `b ≤ ‖z k‖`.
    exact le_trans hb_le_radius (le_of_lt h_radius_lt_norm)


  · -- Backward direction:
    -- Assume the norm sequence is eventually above every
    -- real lower bound.
    intro hnorm r hr

    -- We want to show that eventually `r < ‖z k‖`.
    -- The hypothesis gives non-strict inequalities, so we
    -- apply it to the slightly larger bound `r + 1`.
    obtain ⟨N, hN⟩ := hnorm (r + 1)

    use N

    intro k hk

    -- By the hypothesis, eventually `r + 1 ≤ ‖z k‖`.
    have h_r_plus_one_le_norm : r + 1 ≤ ‖z k‖ := by
      exact hN k hk

    -- Since `r < r + 1`, we get `r < ‖z k‖`.
    have h_r_lt_r_plus_one : r < r + 1 := by
      linarith

    exact lt_of_lt_of_le h_r_lt_r_plus_one
      h_r_plus_one_le_norm


/-
**Mathlib equivalent.**
The equivalent way to define convergence to
the point at infinity is to use the `cocompact` filter
of `ℂ` (the filter of neighbourhoods of `∞` on the
Riemann sphere).

The main idea is:

- A cocompact neighbourhood `s` contains the complement
 of some compact set `K`.
- The norms of points in `K` are bounded above,
  say by `R`.
- If eventually `‖z n‖ > R + 1`, then eventually `z n`
  cannot be in `K`.
-/
theorem convergesToInfinity_iff_tendsto_cocompact
  (z : ℕ → ℂ) :
    ConvergesToInfinity z ↔
      Filter.Tendsto z atTop (Filter.cocompact ℂ)
  := by

  constructor
  · -- Forward direction:
    -- If `‖z n‖ → ∞` in the epsilon sense, then `z`
    -- tends to the cocompact filter.
    intro hz

    -- Unfold the definition of `Tendsto`.
    rw [Filter.tendsto_def]

    -- Let `s` be any cocompact neighbourhood.
    intro s hs

    -- A set belongs to the cocompact filter iff it
    -- contains the complement of some compact set.
    rw [Filter.mem_cocompact] at hs

    -- So there is a compact set `K` such that `Kᶜ ⊆ s`.
    obtain ⟨K, hK_compact, hK_compl_subset⟩ := hs

    -- We want to show that eventually `z n ∈ s`.
    --
    -- Since `K` is compact, the continuous function
    -- `x ↦ ‖x‖` is bounded above on `K`.  We take
    -- the supremum of all norms of points in `K`.
    let R : ℝ := SupSet.sSup
      (Set.image (fun x : ℂ => ‖x‖) K)

    -- The number `R` is nonnegative, because it is the
    -- supremum of a set of nonnegative numbers.
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      apply Real.sSup_nonneg
      rintro y ⟨x, hxK, rfl⟩
      exact norm_nonneg x

    -- Hence `R + 1` is a positive radius.
    have hR_pos : 0 < R + 1 := by
      linarith

    -- Since `z` converges to infinity, eventually
    -- `R + 1 < ‖z n‖`.
    obtain ⟨N, hN⟩ := hz (R + 1) hR_pos

    -- We now prove that eventually `z n ∈ s`.
    have h_eventually_mem : ∃ N, ∀ n ≥ N, z n ∈ s := by
      use N
      intro n hn

      -- For this `n`, the norm is larger than `R + 1`.
      have hnorm_large : R + 1 < ‖z n‖ := hN n hn

      -- It remains to show `z n ∈ s`.
      -- We argue by contradiction.
      by_contra hz_not_mem_s

      -- If `z n ∉ s`, then `z n` cannot lie in `Kᶜ`,
      -- because `Kᶜ ⊆ s`.  Therefore `z n ∈ K`.
      have hz_mem_K : z n ∈ K := by
        by_contra hz_not_mem_K
        have hz_mem_compl : z n ∈ Kᶜ := by
          simpa using hz_not_mem_K
        have hz_mem_s : z n ∈ s :=
          hK_compl_subset hz_mem_compl
        exact hz_not_mem_s hz_mem_s

      -- The image of a compact set under a continuous map
      -- is compact, hence bounded above.
      have h_image_bdd :
          BddAbove (Set.image (fun x : ℂ => ‖x‖) K) := by
        exact (hK_compact.image continuous_norm).bddAbove

      -- Since `z n ∈ K`, its norm belongs to the image set
      have hz_norm_mem_image :
          ‖z n‖ ∈ Set.image (fun x : ℂ => ‖x‖) K := by
        exact Set.mem_image_of_mem
          (fun x : ℂ => ‖x‖) hz_mem_K

      -- Therefore `‖z n‖ ≤ R`, by the defining property
      -- of the supremum.
      have hnorm_le_R : ‖z n‖ ≤ R := by
        dsimp [R]
        exact le_csSup h_image_bdd hz_norm_mem_image

      -- In particular, `‖z n‖ ≤ R + 1`.
      have hnorm_le_R_plus_one : ‖z n‖ ≤ R + 1 := by
        exact le_add_of_le_of_nonneg hnorm_le_R zero_le_one

      -- This contradicts `R + 1 < ‖z n‖`.
      exact not_lt_of_ge hnorm_le_R_plus_one hnorm_large

    -- Membership in `atTop` for a sequence means
    -- “eventually”, i.e. `∃ N, ∀ n ≥ N, ...`.
    simpa [Filter.mem_atTop_sets] using h_eventually_mem


  · -- Backward direction:
    -- If `z` tends to the cocompact filter, then
    -- `‖z n‖ → ∞` in the elementary sense.
    -- We want to show the elementary definition of
    -- convergence to infinity.
    intro hz r hr

    -- Unfold `Tendsto`.
    rw [Filter.tendsto_def] at hz

    -- Consider the set outside the closed ball of
    -- radius `r`.
    let s : Set ℂ := { w : ℂ | r < ‖w‖ }

    -- Show that this set belongs to the cocompact filter.
    have hs_cocompact : s ∈ Filter.cocompact ℂ := by
      rw [Filter.mem_cocompact]

      -- The complement of the closed ball `closedBall 0 r`
      -- is contained in `s`.
      refine ⟨Metric.closedBall (0 : ℂ) r, ?_, ?_⟩

      · -- Closed balls in `ℂ` are compact.
        exact ProperSpace.isCompact_closedBall (0 : ℂ) r

      · -- Show `(closedBall 0 r)ᶜ ⊆ s`.
        intro x hx_notin_closedBall

        -- Not being in the closed ball means
        -- `¬ dist x 0 ≤ r`.
        have hx_not_le : ¬ dist x 0 ≤ r := by
          simpa [Metric.mem_closedBall]
            using hx_notin_closedBall

        -- Hence `r < dist x 0`.
        have hx_lt_dist : r < dist x 0 := by
          exact lt_of_not_ge hx_not_le

        -- Since `dist x 0 = ‖x‖`, we get `r < ‖x‖`.
        show x ∈ s
        dsimp [s]
        simpa [dist_eq_norm] using hx_lt_dist

    -- Since `z` tends to the cocompact filter and `s` is
    -- cocompact, eventually `z n ∈ s`.
    have hpreimage_atTop : z ⁻¹' s ∈ atTop :=
      hz s hs_cocompact

    -- Translate membership in `atTop` into an explicit
    -- eventual statement.
    have h_eventually_mem : ∃ N, ∀ n ≥ N, z n ∈ s := by
      simpa [Filter.mem_atTop_sets] using hpreimage_atTop

    -- Extract the eventual bound.
    obtain ⟨N, hN⟩ := h_eventually_mem

    use N
    intro k hk

    -- Since `z k ∈ s`, by definition of `s`,
    -- we have `r < ‖z k‖`.
    have hzk_mem_s : z k ∈ s := hN k hk
    simpa [s] using hzk_mem_s

end ComplexSequence
