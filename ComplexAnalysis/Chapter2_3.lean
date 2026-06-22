/-

  Linear fractional transformation on
  the extended complex number system

-/


import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import ComplexAnalysis.Chapter2_2


noncomputable section LinearFracTrans

open EComplex

/-
  ## data structure for linear fractional transformation
-/

/--
We represent linear fractional transformation by a
structure consisting of four complex numbers
`a`, `b`, `c`, `d` and an evidence that
`a*d-b*c` is nonzero.
-/
@[ext]
structure LinearFracTrans where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  determinant_ne_zero : a * d - b * c ≠ 0

namespace LinearFracTrans

/-
## the action of linear fractional transformation
-/

/--
  Given a linear fractional transformation
  f(z) = (az + b) / (cz + d), we define its action on an
  extended complex number z as follows:

  f(z) = (az + b) / (cz + d) if cz + d ≠ 0
  f(z) = ∞ if cz + d = 0 and c ≠ 0
  f(∞) = a/c if c ≠ 0
  f(∞) = ∞ if c = 0
-/
def apply (f : LinearFracTrans) (z : EComplex)
  : EComplex :=
  if f.c = 0 then
    match z with
    | EComplex.some z => EComplex.some
        ((f.a / f.d) * z + (f.b / f.d) )
    |  ∞ => ∞
  else
    match z with
    | EComplex.some z=>
      if z = -f.d / f.c then ∞
      else EComplex.some ((f.a * z + f.b)
        / (f.c * z + f.d))
    | ∞ => EComplex.some (f.a / f.c)

/-- The pole of an LFT `f` is the extended complex
  number z such that `f z = ∞`
  With c ≠ 0, the pole  of `f` is -d/c.
  When c = 0, the pole of `f` is ∞.
  Using the convention d/0 = ∞ when d is non-zero,
  the pole can be defined as d/c,
-/
def pole (f : LinearFracTrans) : ℂ
  := -f.d / f.c


/-- Convert the apply function to a coercion,
    so that we can write f z instead of apply f z
-/
instance : CoeFun LinearFracTrans
  (fun _ => EComplex → EComplex) where
  coe f := f.apply

/--
  Applying LFT on complex number z is the same as
  applying LFT on the corresponding term of type EComplex
-/
@[simp]
theorem apply_lft_coe (f : LinearFracTrans) (z : ℂ) :
  f z = f (Option.some z) := rfl


-- define an example of linear fractional transformation
-- f(z) = (1z + 2) / (0z + 1) = z + 2
def f_test1 : LinearFracTrans :=
 { a:= 1, b := 2, c := 0, d:= 1, determinant_ne_zero
 := by simp}

-- testing the function application
-- verify f 3 = 5 , where f is LFT (1z+2) / (0z+1)
example : f_test1 (EComplex.some 3) = EComplex.some 5
  := by
  unfold apply
  have h : f_test1.c = 0 := by rfl
  rw [if_pos h]
  simp
  dsimp [f_test1]
  simp
  norm_num


/-
## Some helper lemmas about nonzero coefficients of LFTs
-/
/-- If c is zero, then a and d are nonzero
-/
lemma a_d_nonzero_of_c_zero {a b c d : ℂ}
  (hdet : a * d - b * c ≠ 0) (hc : c = 0) :
    a ≠  0 ∧ d ≠ 0 := by
  -- determinant is a*d - b*0 = a*d.
  -- Since a*d ≠ 0, d ≠ 0.
  rw [hc] at hdet
  simp only [mul_zero, sub_zero] at hdet
  exact mul_ne_zero_iff.mp hdet

/-- If a is zero, then b and c are nonzero
-/
lemma b_c_nonzero_of_a_zero {a b c d : ℂ}
  (hdet : a * d - b * c ≠ 0) (ha : a = 0) :
    b ≠  0 ∧ c ≠ 0 := by
  rw [ha] at hdet
  simp only [zero_mul, zero_sub] at hdet
  rw [neg_ne_zero] at hdet
  exact mul_ne_zero_iff.mp hdet

-- The value of LFT f in various cases

-- if f.c = 0, then f(∞) = ∞
@[simp]
theorem f_infty_infty
  {f : LinearFracTrans} (hc : f.c = 0) :
    f ∞ = ∞ := by
  simp only [apply, hc, ↓reduceIte]

-- if f.c = 0, then f(z) = (az+b)/d
@[simp]
theorem f_z_azbd
  {f : LinearFracTrans} {z : ℂ} (hc : f.c = 0) :
    f z = (f.a*z+f.b)/f.d := by
  simp only [apply, hc, ↓reduceIte]
  have hd_ne_zero : f.d ≠ 0 :=
    (a_d_nonzero_of_c_zero f.determinant_ne_zero hc).2
  rw [← EComplex.coe_mul, ← EComplex.coe_add]
  rw [← EComplex.coe_div _ _ hd_ne_zero]
  congr
  field_simp

-- if f.c ≠ 0, then f(∞) = a/c
@[simp]
theorem f_infty_a_div_c
  {f : LinearFracTrans} (hc : f.c ≠ 0) :
    f ∞ = f.a/f.c := by
  simp only [apply, hc, ↓reduceIte]
  norm_cast


-- if f.c ≠ 0 and z = -d/c, then f(z) = ∞
@[simp]
theorem f_neg_d_div_c_infty
  {f : LinearFracTrans} (hc : f.c ≠ 0) :
    f (-f.d/f.c) = ∞ := by
  -- Unfold `apply` and use `hc` to show
  -- 'if f.c = 0' is false
  simp only [apply, if_neg hc]
  rw [← EComplex.coe_neg]
  rw [← EComplex.coe_div _ _ hc]
  simp only [↓reduceIte]

-- if f.c ≠ 0 and z ≠ -d/c, then f(z) = (az+b)/(cz+d)
@[simp]
theorem f_value_when_c_nonzero
  {f : LinearFracTrans} {z : ℂ}
    (hc : f.c ≠ 0) (hz : z ≠ -f.d / f.c) :
    f z = (f.a*z + f.b)/(f.c*z + f.d) := by
  simp only [apply, hc, if_neg hz, ↓reduceIte]
  norm_cast
  have h : f.c * z + f.d ≠ 0 := by
    intro hzero
    rw [add_eq_zero_iff_eq_neg] at hzero
    rw [← hzero] at hz
    field_simp at hz
    contradiction
  rw [← EComplex.coe_div _ _ h]


/-- Multiply the difference (z-w) by determinant
-/
lemma apply_sub_apply_num
  (f : LinearFracTrans) (z w : ℂ) :
    (f.a * z + f.b) * (f.c * w + f.d)
    - (f.a * w + f.b) * (f.c * z + f.d) =
    (f.a * f.d - f.b * f.c) * (z - w) := by
  ring





section LFTComposition

/-
## Composition of Linear Fractional Transformation
-/

/--
Given f(z) = (az + b) / (cz + d) and
g(z) = (a'z + b') / (c'z + d'),
we define the composition f ∘ g by:
(f ∘ g)(z) =
(a(a'z + b') + b(c'z + d')) / (c(a'z + b') + d(c'z + d'))

We check that the determinant of the composition
is nonzero, which ensures that the composition is also
a linear fractional transformation.
-/
def comp (f g : LinearFracTrans)
   : LinearFracTrans where
  a := f.a * g.a + f.b * g.c
  b := f.a * g.b + f.b * g.d
  c := f.c * g.a + f.d * g.c
  d := f.c * g.b + f.d * g.d

  determinant_ne_zero := by
    have h3 :
      (f.a * g.a + f.b * g.c) * (f.c * g.b + f.d * g.d)
      - (f.a * g.b + f.b * g.d) * (f.c * g.a + f.d * g.c)
      = (f.a * f.d - f.b *f.c) * (g.a * g.d - g.b * g.c)
    := by ring
    rw [h3]
    exact mul_ne_zero f.determinant_ne_zero
      g.determinant_ne_zero

/-
  ## The identity LFT
-/


/-- The identity linear fractional transformation
  is defined by setting a=d=1 and b=c=0.
-/
def id : LinearFracTrans where
  a := 1
  b := 0
  c := 0
  d := 1
  determinant_ne_zero := by
    simp only [mul_one, mul_zero, sub_zero,
    ne_eq, one_ne_zero, not_false_eq_true]

/-- The linear fractional transformation defined above
 is the identity element for composition of linear
 fractional transformations.
-/
instance : One LinearFracTrans where
  one := id

/-- identity LFT maps ∞ maps to ∞
-/
lemma id_apply_infty :
  (id : LinearFracTrans) ∞ = ∞ := by
  -- Unfold definitions down to the 'apply' function
  dsimp [One.one, id, apply]
  simp only [↓reduceIte]

/--
  Prove that f(z) = z for all z in EComplex
  when f is the identity linear fractional
  transformation defined above.
-/
@[simp]
theorem id_apply (z : EComplex) :
  (id : LinearFracTrans) z = z := by
  -- Unfold definitions
  dsimp [One.one, id, apply]
  -- Simplify the arithmetic coefficients using the
  -- fact that a=1, b=0, c=0, d=1
  simp only [↓reduceIte, ne_eq, one_ne_zero,
    not_false_eq_true, div_self, one_mul, div_one,
    add_zero]
  -- Now the goal is: (match z with ... ) = z
  -- Split into the two cases of EComplex: ∞ (none)
  -- and Finite (some)
  cases z with
  | none => rfl    -- Case ∞: returns ∞
  | some val => rfl
  -- Case Finite: returns val (since 1*val + 0 = val)


/-
  ## Special cases of linear fractional transformation
-/

/--
  A Linear Fractional Transformation is a translation if
  it is of the form f(z) = z + b.
  Normalized form: a=1, c=0, d=1.
-/
def IsTranslation (f : LinearFracTrans) : Prop :=
  f.c = 0 ∧ f.a = f.d

/--
  A Linear Fractional Transformation is linear,
  or is a complex scaling transformation,
  if it is of the form f(z) = az.

When a is a positive real number, it is called a dilation.
When |a|=1, it is a rotation.

  Normalized form: b=0, c=0, d=1.
  (Note: a must be non-zero from determinant condition).
-/
def IsScaling (f : LinearFracTrans) : Prop :=
  f.b = 0 ∧ f.c = 0


/--
  A Linear Fractional Transformation is the standard
  inversion f(z) = 1/z.
  Normalized form: a=0, b=1, c=1, d=0.
-/
def IsInversion (f : LinearFracTrans) : Prop :=
  f.a = 0 ∧ f.d = 0 ∧ f.b = f.c

/--
  A Linear Fractional Transformation is Affine
  if it is of the form f(z) = az + b
  for some nonzero constant a.
  (This corresponds to c=0.)
-/
def IsAffine (f : LinearFracTrans) : Prop :=
  f.c = 0


/--
Constructor for a general LFT
-/
def mk_lft (a b c d : ℂ) (h : a * d - b * c ≠ 0) : LinearFracTrans :=
  { a := a, b := b, c := c, d := d, determinant_ne_zero := h }


/--
Translation transformation z ↦ z + t.
-/
def translation (t : ℂ) : LinearFracTrans :=
  { a := 1, b := t, c := 0, d := 1,
    determinant_ne_zero := by simp }

/--
Scaling transformation z ↦ k * z, where k ≠ 0.
-/
def scaling (k : ℂ) (h : k ≠ 0) : LinearFracTrans :=
  { a := k, b := 0, c := 0, d := 1,
    determinant_ne_zero := by simp [h] }

/--
  Inversion transformation z ↦ 1/z.
  An LFT is an inversion if we set a=d=0 and b=c=1.
-/
def inversion : LinearFracTrans :=
  { a := 0, b := 1, c := 1, d := 0,
    determinant_ne_zero := by simp }


/-- Translation is a special case of affine transformation
-/
theorem IsTranslation_implies_IsAffine (f : LinearFracTrans)
  (h : IsTranslation f) : IsAffine f := by
  -- h : f.c = 0 ∧ f.a = f.d
  -- IsAffine requires f.c = 0
  exact h.1

/-- Scaling is a special case of affine transformation
-/
theorem IsScaling_implies_IsAffine (f : LinearFracTrans)
  (h : IsScaling f) : IsAffine f := by
  -- h : f.b = 0 ∧ f.c = 0
  -- IsAffine requires f.c = 0
  exact h.2

/-- inversion is not affine transformation
-/
theorem IsInversion_implies_NotAffine (f : LinearFracTrans)
  (h : IsInversion f) : ¬ IsAffine f := by
  -- h : f.a = 0 ∧ f.d = 0 ∧ f.b = f.c
  -- det = a*d - b*c = 0 - c*c = -c^2 ≠ 0 => c ≠ 0
  intro h_aff
  rw [IsAffine] at h_aff
  have h_det := f.determinant_ne_zero
  rw [h.1,h.2.1,h.2.2, h_aff, zero_mul, sub_zero] at h_det
  exact h_det rfl


/--   Theorem 2.3.3 (a) iff (b)
  The function induced by a linear fractional transformation
  is an affine transformation if and only if c=0.
-/
theorem IsAffine_iff_affine_action (f : LinearFracTrans) :
  IsAffine f ↔ ∃ A B : ℂ , A ≠ 0 ∧ ∀ (z : ℂ),
    f z = A * z + B := by
  constructor
  · -- Forward: If c=0, then f(z) = (a/d)z + (b/d)
    intro h_affine
    -- Since c=0, a*d ≠ 0 => d ≠ 0 and a ≠ 0
    have h_ad_ne0 : f.a * f.d ≠ 0 := by
      have h_det := f.determinant_ne_zero
      rw [h_affine, mul_zero, sub_zero] at h_det
      exact h_det

    have hd_ne0 : f.d ≠ 0 := by
      exact right_ne_zero_of_mul h_ad_ne0

    use (f.a / f.d), (f.b / f.d)
    constructor
    · have h_frac_ne0 : (f.a / f.d) ≠ 0 := by
        apply div_ne_zero
        · exact left_ne_zero_of_mul h_ad_ne0
        · exact right_ne_zero_of_mul h_ad_ne0
      dsimp [EComplex.some, Zero.zero]
      assumption
    · -- Formula matches
      intro z
      -- Use the earlier lemma f_z_azbd (f.c = 0)
      rw [f_z_azbd h_affine]
      norm_cast
      field_simp [right_ne_zero_of_mul h_ad_ne0]
  · -- Backward: If f(z) = Az + B, then c=0
    rintro ⟨A, B, hA, h_eq⟩
    by_contra hc_ne0
    have hc_ne0_val : f.c ≠ 0 := hc_ne0
    -- If c ≠ 0, then at z = -d/c, f(z) = ∞
    let z_pole := -f.d / f.c
    have h_pole : f z_pole = ∞ := by
      have h_coe: ((-↑f.d / ↑f.c) : EComplex)
        = EComplex.some (-f.d / f.c) := by norm_cast
      rw [← h_coe]
      exact f_neg_d_div_c_infty hc_ne0_val
    -- But the formula says f(z) = Az + B (finite)
    have h_finite : f z_pole = A * z_pole + B
      := h_eq z_pole
    -- Contradiction: ∞ = finite
    rw [h_finite] at h_pole
    contradiction

/--  Theorem 2.3.3 (b) iff (c)
  An LFT f is affine if and only if f(∞) = ∞.
-/
theorem IsAffine_iff_infty (f : LinearFracTrans) :
  f.IsAffine ↔ f EComplex.infty = EComplex.infty := by
    -- By definition of IsAffine, we know that f.c = 0.
    simp only [IsAffine]
    -- By definition of f, we know that
    -- f (infty) = infty if and only if f.c = 0.
    simp only [apply, ite_eq_left_iff, reduceCtorEq,
      imp_false, Decidable.not_not]


/-- #### Theorem 2.3.3
  Given a linear fractional transformation. The following
  are equivalent:

  (a) the coefficients `c` in `f` is equal to 0.
  (b) When the domain is restricted to the finite complex
      plane, `f` is an affine transformation.
  (c) The point at infinity is mapped to itself.
-/
theorem isAffine_tfae (f : LinearFracTrans) : List.TFAE
 [IsAffine f,
 ∃ A B : ℂ , A ≠ 0 ∧ ∀ (z : ℂ), f z = A * z + B,
  f EComplex.infty = EComplex.infty] := by
  tfae_have 1 ↔ 2 := IsAffine_iff_affine_action f
  tfae_have 1 ↔ 3 := IsAffine_iff_infty f
  tfae_finish



/- #### Theorem 2.3.4 Case 1
When c=0, the linear fractional transformation can be
decomposed into dilation and translation.
-/
lemma decomposition_affine
  (f : LinearFracTrans) (hc : f.c = 0) :
  let s_a := scaling f.a (by
    have h := f.determinant_ne_zero
    rw [hc] at h
    simp only [mul_zero, sub_zero, ne_eq,
      mul_eq_zero, not_or] at h
    exact h.1)
  let t_b := translation f.b
  let s_d := scaling f.d (by
    have h := f.determinant_ne_zero
    rw [hc] at h
    simp only [mul_zero, sub_zero, ne_eq, mul_eq_zero,
      not_or] at h
    exact h.2)
  let i := inversion
  f = (i.comp (s_d.comp i)).comp (t_b.comp s_a) := by
    simp [comp, inversion, scaling, translation ]
    ring_nf at *
    ext <;> simp_all only

/-- #### Theorem 2.3.4 Case 2
Decomposition of a linear fractional transformation
Assume c ≠ 0. Decompose an LFT into translation,
dilation, and inversion. When c≠0, the decomposition is

	\frac{az+b}{cz+d}
  = \frac{a}{c} + \frac{bc-ad}{c} \frac{1}{cz+d}.
-/
lemma decomposition_nonaffine
  (f : LinearFracTrans) (hc : f.c ≠ 0) :
  let t1 := translation (f.a / f.c)
  let k := (f.b * f.c - f.a * f.d) / f.c
  let s1 := scaling k (by
    simp +zetaDelta only [ne_eq, div_eq_zero_iff, not_or]
    exact ⟨ fun h => f.determinant_ne_zero <|
      by linear_combination -h, hc ⟩)
  let i := inversion
  let t2 := translation f.d
  let s2 := scaling f.c hc
  f = t1.comp (s1.comp (i.comp (t2.comp s2))) := by
    unfold comp translation scaling inversion;
    simp --
    ring_nf
    simp_all only [ne_eq, not_false_eq_true,
      mul_inv_cancel_right₀, mul_inv_cancel₀, one_mul]


/--
Define the property of being decomposable into basic
transformations.
-/
inductive IsDecomposable : LinearFracTrans → Prop
| translation (t : Complex) :
    IsDecomposable (LinearFracTrans.translation t)
| scaling (k : Complex) (h : k ≠ 0) :
    IsDecomposable (LinearFracTrans.scaling k h)
| inversion : IsDecomposable LinearFracTrans.inversion
| comp (f g : LinearFracTrans) :
    IsDecomposable f → IsDecomposable g →
    IsDecomposable (f.comp g)


/-- #### Theorem 2.3.4
Every linear fractional transformation can be decomposed
into a finite sequence of fundamental transformations:
translations, non-zero scalings, and inversions.

This theorem establishes that the basic transformations
form a generating set for the group of linear fractional
transformations (Möbius transformations).

The proof proceeds by case analysis on the coeff. `f.c`:

- **Affine case (`f.c = 0`):** The transformation maps
infinity to infinity and reduces to a scaling and a
translation (handled via `decomposition_affine`).

- **Non-affine case (`f.c ≠ 0`):** The transformation maps
a finite pole to infinity. It is decomposed into the
standard sequence of operations: forming the denominator
(scaling and translation), applying an inversion, and
adjusting the numerator (a second scaling and translation,
handled via `decomposition_nonaffine`).
-/
theorem isDecomposable (f : LinearFracTrans)
  : IsDecomposable f := by
  by_cases hc : f.c = 0
  · let decomp :=
      LinearFracTrans.decomposition_affine f hc
    rw [decomp]
    apply IsDecomposable.comp
    · apply IsDecomposable.comp
      · apply IsDecomposable.inversion
      · apply IsDecomposable.comp
        · apply IsDecomposable.scaling
        · apply IsDecomposable.inversion
    · apply IsDecomposable.comp
      · apply IsDecomposable.translation
      · apply IsDecomposable.scaling
  · -- Case c ≠ 0
    -- We use the decomposition theorem for nonaffine LFT
    rw [decomposition_nonaffine f hc]
    -- The RHS is a composition of basic transformations
    -- f = t1.comp (s1.comp (i.comp (t2.comp s2)))
    apply IsDecomposable.comp
    · apply IsDecomposable.translation
    · apply IsDecomposable.comp
      · apply IsDecomposable.scaling
      · apply IsDecomposable.comp
        · apply IsDecomposable.inversion
        · apply IsDecomposable.comp
          · apply IsDecomposable.translation
          · apply IsDecomposable.scaling




/-
  ## Composition of linear fractional transformations
-/

-------------------------------------------------------------
---     Helper lemmas for the proof about composition of LFTs
-------------------------------------------------------------

private lemma case11 {f g : LinearFracTrans} {z : EComplex}
  (hf : f.c = 0) (hg : g.c = 0)
  : (comp f g) z = f (g z) := by
  -- In this case, all three transformations are affine.
  -- The composition is also affine, and the formula simplifies
  -- significantly.
  have h_comp : (comp f g).c = 0 := by
    simp only [comp]
    rw [hf, hg]
    simp
  cases z with
  | none =>
  -- Case z = ∞.
  -- Since c=0, apply returns ∞. So ∞ = ∞.
      simp only [apply, hf, hg, h_comp, if_true]
  | some z =>
    have hd_f : f.d ≠ 0 :=
      (a_d_nonzero_of_c_zero f.determinant_ne_zero hf).2
    have hd_g : g.d ≠ 0 :=
      (a_d_nonzero_of_c_zero g.determinant_ne_zero hg).2
    have hd_comp : (comp f g).d ≠ 0 := by
      simp only [comp, ne_eq]
      intro hd_zero
      rw [hf] at hd_zero
      simp only [zero_mul, zero_add, mul_eq_zero] at hd_zero
      obtain h1|h2 := hd_zero <;>
      · contradiction
    -- 1. Rewrite LHS: (comp f g) z
    rw [← apply_lft_coe]
    rw [@f_z_azbd (comp f g) _ h_comp]
    -- 2. Rewrite RHS: f (g z)
    --    First rewrite inner g z
    rw [← apply_lft_coe]
    rw [@f_z_azbd g _ hg]
    -- 3. Now rewrite outer f (...).
    norm_cast
    rw [@f_z_azbd f _ hf]
    -- 4. Solve the algebra
    norm_cast
    dsimp [comp] -- Expand the def. of comp.a, comp.b, etc.
    have h1_nonzero : f.c * g.b + f.d * g.d ≠ 0 := by
      rw [hf] ; ring_nf
      exact (mul_ne_zero_iff_right hd_g).mpr hd_f
    have h2_nonzero : g.b * f.c + g.d * f.d ≠ 0 := by
      rw [hf] ; ring_nf
      exact (mul_ne_zero_iff_right hd_f).mpr hd_g
    rw [hf, hg]
    field_simp [hd_f, hd_g, hd_comp, h1_nonzero, h2_nonzero]
    -- Clear denominators
    ring

-- When lft f is affine and lft g is not affine,
-- then the composition f ∘ g is not affine.
private lemma comp_f_g_not_affine1 {f g : LinearFracTrans}
  (hf : f.c = 0) (hg : g.c ≠ 0) : (comp f g).c ≠ 0 := by
  -- 1. Unfold the definition of composition for 'c'
  --    (comp).c = f.c * g.a + f.d * g.c
  simp only [comp]
  -- 2. Substitute f.c = 0. The formula becomes: 0 + f.d * g.c
  rw [hf, zero_mul, zero_add]
  -- 3. To prove f.d * g.c ≠ 0, we need both f.d ≠ 0 and g.c ≠ 0.
  apply mul_ne_zero
  · -- Prove f.d ≠ 0 using the determinant condition of f
    -- det = a*d - b*c ≠ 0. With c=0, a*d ≠ 0, so d ≠ 0.
    have h_det := f.determinant_ne_zero
    rw [hf] at h_det
    simp only [mul_zero, sub_zero, ne_eq] at h_det
    exact right_ne_zero_of_mul h_det  -- Extract d ≠ 0
  · -- Prove g.c ≠ 0 (Given directly)
    exact hg


-- When lft g is affine and lft f is not affine,
-- then the composition f ∘ g is not affine.
private lemma comp_f_g_not_affine2 {f g : LinearFracTrans}
  (hf : f.c ≠ 0) (hg : g.c = 0) : (comp f g).c ≠ 0 := by
  simp only [comp]
  rw [hg, mul_zero, add_zero]
  apply mul_ne_zero
  · assumption
  · have h_det := g.determinant_ne_zero
    rw [hg] at h_det
    simp only [mul_zero, sub_zero, ne_eq] at h_det
    exact left_ne_zero_of_mul h_det  -- Extract d ≠ 0


-- if z is a pole of g, then z is also a pole of the composition f ∘ g,
--  and both sides equal ∞
private lemma case121 {f g : LinearFracTrans} {z : EComplex}
  (hf : f.c = 0) (hg : g.c ≠ 0) (h_comp : (comp f g).c ≠ 0)
  (h_pole : g.c * z + g.d = 0)
  : (comp f g) z = f (g z) := by
  have h_d_nonzero : f.d ≠ 0 := (a_d_nonzero_of_c_zero f.determinant_ne_zero hf).2
  -- Verify z must be finite (since ∞ is not a pole)
  cases z with
  | none =>
    -- g.c * ∞ + g.d = ∞ + g.d = ∞. Since ∞ ≠ 0, this case is impossible.
    contradiction
  | some z =>
    -- z is finite. h_pole says: g.c * z + g.d = 0
    have h_z_val : z = -g.d / g.c := by
      -- Solve g.c * z + g.d = 0
      have hs : (EComplex.some (g.c * z + g.d) : EComplex) = (EComplex.some 0 : EComplex) := by
        -- LHS: (↑g.c) * (some z) + (↑g.d)  ↦  some (g.c*z + g.d)
        -- RHS: 0 ↦ some 0
        push_cast
        assumption
      have : g.c * z + g.d = 0 := EComplex.coe_eq_coe_iff.mp hs
      field_simp
      rw [eq_neg_iff_add_eq_zero, mul_comm]
      assumption
    -- Evaluate RHS: f (g z)
    -- Since denominator is 0, g z = ∞
    rw [apply]
    --simp only [hg, h_pole, if_false, ite_true] -- simplify g's apply
    --    f ∞ = ∞ (because f.c = 0)
    rw [← f_infty_infty  hf]
    -- Evaluate LHS: (comp f g) z
    -- We claim z is also the pole for the composition
    rw [apply]
    simp only [h_comp, if_false] -- simplify comp's apply (it's not affine)

    -- We need to compute the coefficients of the composition (comp f g).
    have h_comp_d : (comp f g).d  = f.d * g.d := by
      unfold comp
      simp only [add_eq_right, mul_eq_zero]
      left
      exact hf
    have h_comp_c : (comp f g).c  = f.d * g.c := by
      unfold comp
      simp only [add_eq_right, mul_eq_zero]
      left
      exact hf
    -- Show that z is also a pole of the composite function (comp f g)
    have hh : z = -(comp f g).d / (comp f g).c  := by
      rw [h_comp_c, h_comp_d]
      rw [h_z_val]
      field_simp [h_d_nonzero]
    -- Since z is a pole, the function returns ∞
    rw [if_pos hh]
    simp [apply, hf, hg, h_z_val]

private lemma case122 {f g : LinearFracTrans} {z : EComplex}
  (hf : f.c = 0) (hg : g.c ≠ 0) (h_comp : (comp f g).c ≠ 0)
  (h_non_pole : g.c * z + g.d ≠ 0)
  : (comp f g) z = f (g z) := by
  have hd_f : f.d ≠ 0 := (a_d_nonzero_of_c_zero f.determinant_ne_zero hf).2
  cases z with
  | none =>
      -- z = ∞
      -- g(∞)=a/c since g.c≠0; f is affine so f maps
      -- finite to finite; comp has c≠0 so comp(∞)=a/c
      -- just simplify and do algebra
      simp only [apply, comp, hf, zero_mul, zero_add,
        mul_eq_zero, hd_f, hg, or_self, ↓reduceIte]
           -- goal is now an equality of `some _ = some _`
      congr
      field_simp [hg, hd_f]

  | some z =>
      -- Turn the non-pole hypothesis into a ℂ statement: g.c*z + g.d ≠ 0
      have hczd_ne0 : g.c * z  + g.d ≠ 0 := by
        intro h0
        apply h_non_pole
        -- show (↑(g.c*z+g.d) : EComplex) = 0
        have : (EComplex.some (g.c * z + g.d) : EComplex) = 0 := by
          exact congrArg EComplex.some h0
        change ((g.c * z + g.d : ℂ) : EComplex) = 0
        simpa [EComplex.add, EComplex.mul] using this

      -- hence z is not the pole -g.d/g.c
      have hz_notpole : z ≠ -g.d / g.c := by
        intro hz
        apply hczd_ne0
        subst hz
        field_simp [hg]
        ring

      -- and z is not the pole of the composition either
      have hz_notpole_comp : z ≠ -(comp f g).d / (comp f g).c := by
        intro hzcomp
        have hratio : -(comp f g).d / (comp f g).c = -g.d / g.c := by
          dsimp [comp]
          rw [hf]
          field_simp [hg, hd_f]
          ring
        apply hz_notpole
        exact by simpa [hratio] using hzcomp

      -- also need denominator of comp at z is nonzero for field_simp
      have hden_comp : (comp f g).c * z + (comp f g).d ≠ (0 : ℂ) := by
        dsimp [comp]
        rw [hf]
        have hfac :
            (f.d * g.c) * z + f.d * g.d = f.d * (g.c * z + g.d) := by ring
        intro h0
        have h0' : f.d * (g.c * z + g.d) = 0 := by
          simpa [hfac] using h0
        rcases mul_eq_zero.mp h0' with hfd | hczd
        · exact hd_f hfd
        · exact hczd_ne0 hczd

      -- We need to compute the coefficients of the composition (comp f g).
      have h_comp_a : (comp f g).a = f.a * g.a + f.b * g.c := by
        simp [comp]
      have h_comp_b : (comp f g).b = f.a * g.b + f.b * g.d := by
        simp [comp]
      have h_comp_d : (comp f g).d  = f.d * g.d := by
        unfold comp
        simp only [add_eq_right, mul_eq_zero]
        left
        exact hf
      have h_comp_c : (comp f g).c  = f.d * g.c := by
        unfold comp
        simp only [add_eq_right, mul_eq_zero]
        left
        exact hf

      -- Show that z is also a pole of the composite
      -- function (comp f g)
      have hz_pole_comp : z ≠ -(comp f g).d / (comp f g).c
        := by
        rw [h_comp_c, h_comp_d]
        intro h_contradiction
        have hcancel :
          (f.d * g.d) / (f.d * g.c) = g.d / g.c := by
          -- cancels the common factor `f.d`
          -- using hd_f : f.d ≠ 0
          simpa [mul_assoc]
            using (mul_div_mul_left g.d g.c hd_f)
        have :
          -(f.d * g.d) / (f.d * g.c) = -g.d / g.c := by
          calc
          -(f.d * g.d) / (f.d * g.c)
              = -((f.d * g.d) / (f.d * g.c))
                := by simp [neg_div]
          _   = -(g.d / g.c) := by simp [hcancel]
          _   = -g.d / g.c := by simp [neg_div]
        rw [this] at h_contradiction
        contradiction

      -- Now just compute both sides via `apply`
      -- and finish by algebra
      simp only [apply]
      simp [hf, hg, hz_notpole, h_comp, hz_pole_comp]
      field_simp [hczd_ne0]
      rw [mul_comm] at hczd_ne0
      field_simp [hczd_ne0]
      rw [mul_comm] at hden_comp
      field_simp [hden_comp]
      rw [h_comp_a, h_comp_b, h_comp_c, h_comp_d]
      ring

/-- f.c ≠ 0, g.c = 0, and z is not a pole of
    the composition f ∘ g
-/
private lemma case211
  {f g : LinearFracTrans} {z : EComplex}
  (hf : f.c ≠ 0) (hg : g.c = 0) (h_comp : (comp f g).c ≠ 0)
  (h_pole : f.c * g.a * z + (f.c * g.b + f.d * g.d) = 0)
  : (comp f g) z = f (g z) := by

  have hd_g : g.d ≠ 0
    := (a_d_nonzero_of_c_zero g.determinant_ne_zero hg).2
  -- show that z is a pole of f.
  -- z cannot be ∞ if it satisfies a finite pole equation
  cases z with
  | none =>
      contradiction
  | some z =>
      -- 1) Show z is a pole of the composition:
      -- z = -(comp.d)/(comp.c)
      have hz_comp :
        z = -(comp f g).d / (comp f g).c := by
        -- Turn the EComplex equation into a
        -- ℂ equation and solve it
        have hC :
          f.c * g.a * z + (f.c * g.b + f.d * g.d) = (0 : ℂ)
          := by
          apply Option.some.inj
          assumption

        -- Now use comp.c = f.c*g.a,
        -- comp.d = f.c * g.b + f.d * g.d (since g.c=0)
        have hc' : (comp f g).c = f.c * g.a := by
          simp [comp, hg]
        have hd' :
          (comp f g).d = f.c * g.b + f.d * g.d := by
          simp [comp, hg]

        -- Solve (comp.c)*z + (comp.d) = 0
        -- ->  z = -comp.d/comp.c
        -- using hc' hd' and hf/h_comp for nonzero
        -- (We need (comp f g).c ≠ 0, which is h_comp.)
        -- Rearrange:
        have : (comp f g).c * z + (comp f g).d = 0 := by
          -- rewrite hC into this form
          simpa [hc', hd', mul_assoc, add_assoc] using hC
        -- solve for z
        -- from (comp.c)*z + comp.d = 0
        -- => z = -comp.d/comp.c
        have : (comp f g).c * z = -(comp f g).d := by
          exact eq_neg_of_add_eq_zero_left this
        -- divide by (comp f g).c
        -- (eq_div_iff h_comp).2 requires z * c = ...
        have : z * (comp f g).c = -(comp f g).d
          := by simpa [mul_comm] using this
        exact (eq_div_iff h_comp).2 this

      -- 2) Compute both sides: they are ∞

      -- LHS is ∞ because z is the pole of comp
      have hL : (comp f g) (EComplex.some z) = ∞ := by
        -- the lemma f_neg_d_div_c_infty is phrased
        -- for input -d/c, so we use apply directly.
        simp [apply, h_comp, hz_comp]

      -- RHS: first compute g z (affine),
      -- then show it equals the pole of f
      have hgz : g z = (g.a * z + g.b) / g.d := by
        simpa using (f_z_azbd (f := g) (z := z) hg)

      -- show g(z) is the pole of f, i.e. g(z) = -f.d/f.c
      have h_gz_pole : ((g.a * z + g.b) / g.d) = -f.d / f.c := by
        -- from the pole equation: f.c*(g.a*z+g.b)/g.d + f.d = 0
        -- derive in ℂ using hC again
        have hC : f.c * (g.a * z + g.b) + f.d * g.d = (0 : ℂ) := by
          -- this is hC but re-associated
          have hC0 : f.c * g.a * z + (f.c * g.b + f.d * g.d) = (0 : ℂ) := by
            apply Option.some.inj
            --simpa [EComplex.add, EComplex.mul, add_assoc, add_left_comm, add_comm, mul_assoc] using h_pole
            assumption

          -- reassociate to f.c*(g.a*z+g.b) + f.d*g.d = 0
          have : f.c * (g.a * z + g.b) + f.d * g.d = 0 := by
            -- expand and match
            --nlinarith [hC0]  -- or: `ring_nf` style; if nlinarith fails, use `ring` with `simp` lemmas
            ring_nf
            ring_nf at hC0
            assumption
          exact this

        -- divide by g.d and solve:
        have : f.c * ((g.a * z + g.b) / g.d) + f.d = 0 := by
          -- divide the equation by g.d (using hd_g)
          field_simp [hd_g] at hC
          -- hC is already cleared; do the intended step directly:
          have : f.c * ((g.a * z + g.b) / g.d) = -f.d := by
            have : f.c * (g.a * z + g.b) = -(f.d * g.d) := by
              exact eq_neg_of_add_eq_zero_left hC
            -- divide by g.d
            -- (a = b) -> (a/g.d = b/g.d)
            -- then rewrite by using field_simp
            field_simp [hd_g] at this
            field_simp [hd_g] at *
            simpa [mul_assoc] using this

          -- add f.d both sides
          -- actually we want + f.d = 0:
          -- from X = -f.d, we get X + f.d = 0
          exact by simp [this]

        -- Solve f.c * w + f.d = 0 => w = -f.d/f.c
        have : f.c * ((g.a * z + g.b) / g.d) = -f.d := by
          exact eq_neg_of_add_eq_zero_left this
        have : ((g.a * z + g.b) / g.d) * f.c = -f.d := by simpa [mul_comm] using this
        exact (eq_div_iff hf).2 (by simpa [mul_comm, neg_div] using this)

      -- therefore f (g z) = ∞
      have hR : f (g (EComplex.some z)) = ∞ := by
        -- rewrite g(some z) to the value, then use the pole lemma for f
        -- (f_neg_d_div_c_infty expects input -f.d/f.c)
        -- so turn g z into that and simp
        simp [apply, hg, hf]
        field_simp [hd_g]
        field_simp [hd_g] at h_gz_pole
        assumption

      -- Finish
      simpa using (by
        -- use computed LHS/RHS
        simp [hL, hR])

private lemma case212 {f g : LinearFracTrans} {z : EComplex}
  (hf : f.c ≠ 0) (hg : g.c = 0) (h_comp : (comp f g).c ≠ 0)
  (h_not_pole : f.c * g.a * z + (f.c * g.b + f.d * g.d) ≠ 0)
  : (comp f g) z = f (g z) := by
  -- from det(g) and g.c=0 we get g.a≠0 and g.d≠0
  have hga_ne : g.a ≠ 0 := (a_d_nonzero_of_c_zero g.determinant_ne_zero hg).1
  have hgd_ne : g.d ≠ 0 := (a_d_nonzero_of_c_zero g.determinant_ne_zero hg).2

  cases z with
  | none =>
      -- z = ∞
      -- g ∞ = ∞ (since g.c = 0), so RHS = f ∞ = a/c.
      -- LHS = (comp f g) ∞ = comp.a/comp.c, and with g.c=0 that
      -- simplifies to (f.a*g.a)/(f.c*g.a) = f.a/f.c.
      simp only [apply, comp, hg, mul_zero, add_zero,
        mul_eq_zero, hf, false_or, ↓reduceIte]
      -- goal is now an equality of coerced complex numbers
      -- cancel g.a
      simp [hga_ne]
      field_simp [hga_ne]

  | some z =>
      -- Turn h_not_pole into a ℂ inequality on the denominator:
      have hdenC : f.c * g.a * z + (f.c * g.b + f.d * g.d) ≠ (0 : ℂ) := by
        intro h0
        apply h_not_pole
        -- show the EComplex expression is 0
        exact congrArg EComplex.some h0

      -- hence z is not the pole of comp: z ≠ -(comp.d)/(comp.c)
      have hz_notpole_comp : z ≠ -(comp f g).d / (comp f g).c := by
        intro hz0
        -- rewrite pole equality using g.c = 0
        have hz0' :
            z = -(f.c * g.b + f.d * g.d) / (f.c * g.a) := by
          -- simp expands comp.c and comp.d under hg
          simpa [comp, hg, mul_assoc, add_assoc] using hz0
        -- then the denominator must be 0, contradiction with hdenC
        have : f.c * g.a * z + (f.c * g.b + f.d * g.d) = 0 := by
          -- substitute z and clear denominators (need f.c*g.a ≠ 0)
          have hcga : f.c * g.a ≠ 0 := mul_ne_zero hf hga_ne
          rw [hz0']
          field_simp [hcga]
          ring
        exact hdenC this

      -- define the affine value w = g(z) (as a complex number)
      let w : ℂ := (g.a * z + g.b) / g.d

      -- show w is not a pole of f
      have hw_notpole : w ≠ -f.d / f.c := by
        intro hw
        -- clear denominators in hw
        have hw' : (g.a * z + g.b) * f.c = (-f.d) * g.d := by
          -- expand w and clear g.d and f.c
          have := hw
          dsimp [w] at this
          field_simp [hgd_ne, hf] at this
          simpa [mul_assoc, mul_comm, mul_left_comm] using this
        -- convert to f.c*g.a*z + (f.c*g.b + f.d*g.d) = 0
        have : f.c * g.a * z + (f.c * g.b + f.d * g.d) = 0 := by
          -- from hw' get f.c*(g.a*z+g.b) + f.d*g.d = 0, then expand
          have hw'' : f.c * (g.a * z + g.b) = -(f.d * g.d) := by
            -- rearrange hw'
            calc
              f.c * (g.a * z + g.b) = (g.a * z + g.b) * f.c := by ring
                                  _ = -f.d * g.d := by rw [hw']
                                  _ = -(f.d * g.d) := by ring

          have : f.c * (g.a * z + g.b) + f.d * g.d = 0 :=
            (eq_neg_iff_add_eq_zero).1 (by simpa [neg_mul, mul_assoc] using hw'')
          -- expand f.c*(g.a*z+g.b)
          -- and rewrite into the target shape
          calc
              f.c * g.a * z + (f.c * g.b + f.d * g.d)
            _=f.c * (g.a * z + g.b) + f.d * g.d := by ring
            _=0 := by rw [this]
        exact hdenC this

      -- Now rewrite both sides to the same complex value and finish by algebra
      rw [← apply_lft_coe (f := comp f g) (z := z)]
      rw [← apply_lft_coe (f := g) (z := z)]
      rw [f_value_when_c_nonzero (f := comp f g) (z := z) h_comp hz_notpole_comp]
      rw [f_z_azbd (f := g) (z := z) hg]
      norm_cast

      -- make the argument visibly `some w`
      change ↑((f.comp g).a * z + (f.comp g).b) / ↑((f.comp g).c * z + (f.comp g).d) = f.apply ↑w
      simp [apply, hf]

      -- turn f (some w) into f w and apply the “c≠0” formula
      simp [hw_notpole]
      -- rw [← apply_lft_coe (f := f) (z := w)]
      -- rw [← f_value_when_c_nonzero (f := f) (z := w) hf hw_notpole]

      -- Reduce to a complex identity and finish by algebra
      -- norm_cast
      dsimp [w, comp]
      simp [hg]
      norm_cast

      rw [← EComplex.coe_eq_coe_iff]
      have h_ne_1 : f.c * g.a * z + (f.c * g.b + f.d * g.d) ≠ 0:= by
        have : f.c * g.a * z + (f.c * g.b + f.d * g.d) =f.c * g.a * z + (f.c * g.b + f.d * g.d)
          := by ring
        rwa [this]

      field_simp
      ring_nf

private lemma case221 {f g : LinearFracTrans} {z : EComplex}
  (hf : f.c ≠ 0) (hg : g.c ≠ 0) (h_comp : (comp f g).c = 0)
    : (comp f g) z = f (g z) := by
  -- We first do some simple arithemtic to be used later
  have hrel : f.c * g.a + f.d * g.c = 0 := by
    simpa [comp] using h_comp

  -- We will need (comp f g).d ≠ 0 (since comp is a valid LFT and comp.c=0)
  have hd_comp : (comp f g).d ≠ 0 :=
    (a_d_nonzero_of_c_zero (comp f g).determinant_ne_zero h_comp).2

  have hd_comp' : g.b * f.c + g.d * f.d ≠ 0 := by
    -- 1. Unfold the definition of comp.d
    --    (comp f g).d = f.c * g.b + f.d * g.d
    dsimp [comp] at hd_comp

    -- 2. Rearrange terms to match g.b * f.c + g.d * f.d
    --    hd_comp is: f.c * g.b + f.d * g.d ≠ 0
    rw [mul_comm g.b, mul_comm g.d]
    exact hd_comp

  have hd_comp_a : (comp f g).a ≠ 0 :=
    (a_d_nonzero_of_c_zero (comp f g).determinant_ne_zero h_comp).1

  have h_fcga : f.c * g.a = -(f.d * g.c) :=
    eq_neg_of_add_eq_zero_left hrel

  cases z with
  | none =>
      -- The compositie LFT is an affine function
      -- It will maps ∞ to ∞

      -- LHS: affine => ∞
      have hL : (comp f g) (∞ : EComplex) = ∞ := by
        exact f_infty_infty h_comp

      -- RHS: g(∞) = g.a/g.c. Using comp.c=0 we show g.a/g.c = -f.d/f.c, so f(g∞)=∞.
      have hga : g.a / g.c = -f.d / f.c := by
        have h1 : f.c * g.a = -(f.d * g.c) :=
          eq_neg_of_add_eq_zero_left hrel
        -- clear denominators in the goal
        field_simp [hf, hg]
        -- goal becomes `f.c * g.a = -(f.d * g.c)` up to commutativity
        simpa [mul_comm, mul_left_comm, mul_assoc] using h1

      have hR : f (g (∞ : EComplex)) = ∞ := by
        -- g ∞ is finite; f sends that particular finite value to ∞
        -- because it equals the pole -f.d/f.c
        simp only [apply, hf, ↓reduceIte, hg, hga]

      simp [hL, hR]

  | some z =>
      -- z is finite: split on whether z is the pole of g

      by_cases hz : z = -g.d / g.c
      · -- Case 1
        --
        -- When z=-g.d/g.c, z will eventually goes to f.a/f.c via ∞
        subst hz
        -- RHS: g(pole)=∞, so f(g(pole)) = f(∞) = f.a/f.c
        have hR : f (g (EComplex.some (-g.d / g.c)))  = (f.a / f.c : ℂ∞) := by
          -- first compute g at its pole
          have h0: g (-g.d / g.c) = (∞ : EComplex) := by
            simpa only using (f_neg_d_div_c_infty (f := g) hg)
          -- move from ℂ-input to EComplex-input
          have : g (EComplex.some (-g.d / g.c)) = (∞ : EComplex) := by
            have harg : (↑(-g.d / g.c) : EComplex) = (-↑g.d : EComplex) / (↑g.c : EComplex) := by
            -- coe_div: ↑((-g.d)/g.c) = (↑(-g.d))/ (↑g.c)
            -- then coe_neg: ↑(-g.d) = -↑g.d
              simpa only [EComplex.coe_neg] using (EComplex.coe_div (-g.d) g.c hg)
            have h0' : g.apply (↑(-g.d / g.c) : EComplex) = (∞ : EComplex) := by
              simpa only [harg] using h0
            simpa only [apply, ↓reduceIte, ite_eq_right_iff,
              reduceCtorEq, imp_false, ne_eq]
          -- now apply f to ∞
          simp only [this, f_infty_a_div_c (f := f) hf]

        -- LHS: comp is affine (c=0), so use f_z_azbd and show it equals f.a/f.c
        have hL :
            (comp f g) (EComplex.some (-g.d / g.c)) = (f.a / f.c : ℂ∞) := by
          -- rewrite to ℂ input, then use affine formula
          change (comp f g).apply (EComplex.some (-g.d / g.c)) = (f.a / f.c : ℂ∞)
          rw [f_z_azbd (f := comp f g) (z := -g.d / g.c) h_comp]
          -- now it's a pure ℂ identity
          norm_cast
          dsimp [comp]
          -- use comp.c=0 as hrel; clear denominators
          have : (g.b * f.c + g.d * f.d) ≠ 0 := by
            intro h0
            apply hd_comp
            -- turn h0 into the standard ordering
            -- f.c*g.b + f.d*g.d = 0
            have h0' : f.c * g.b + f.d * g.d = 0 := by
              simpa only [mul_comm, mul_left_comm, mul_assoc,
                add_comm, add_left_comm, add_assoc] using h0
            -- now rewrite (comp f g).d
            simpa only [comp] using h0'

          field_simp [hf, hg, hd_comp, this]
          ring_nf

          have h_main : -(f.a * g.a * g.d * f.c)
                        = f.a * g.c * g.d * f.d := by
            calc
              -(f.a * g.a * g.d * f.c)
                  = f.a * g.d * (-(f.c*g.a)) := by ring
              _   = f.a * g.d * (-(-(f.d * g.c))) := by rw [h_fcga]
              _   = f.a * g.c * g.d * f.d := by ring

          simp [h_main]

        -- Check that LHS and RHS are equal after some cosmetic changes
        have hL': (f.comp g).apply (EComplex.some (-g.d / g.c)) = (f.comp g).apply ↑(-g.d / g.c)
          := by simp
        have hR':  f.apply (g.apply (EComplex.some (-g.d / g.c))) = f.apply (g.apply ↑(-g.d / g.c))
          := by simp
        rw [hL', hR', hL, hR]

      · -- Case 2
        -- hz : z ≠ -g.d/g.c (non-pole of g)
        have hden_g : g.c * z + g.d ≠ (0 : ℂ) := by
          intro h0
          apply hz
          have hz' : g.c * z = -g.d := eq_neg_of_add_eq_zero_left h0
          have hz'' : z * g.c = -g.d := by simpa [mul_comm] using hz'
          exact (eq_div_iff hg).2 (by simpa [mul_comm] using hz'')

        -- Let w = g(z)
        let w : ℂ := (g.a * z + g.b) / (g.c * z + g.d)

        -- Show w is not the pole of f; otherwise comp.d = 0, contradicting hd_comp
        have hw : w ≠ -f.d / f.c := by
          intro hw0
          -- Clear denominators in hw0:
          have hw1 : f.c * (g.a * z + g.b) + f.d * (g.c * z + g.d) = 0 := by
            -- from w = -f.d/f.c
            dsimp [w] at hw0
            field_simp [hf, hden_g] at hw0
            -- hw0 becomes: f.c*(g.a*z+g.b) = -(f.d)*(g.c*z+g.d)
            -- move RHS to LHS
            have : f.c * (g.a * z + g.b) + f.d * (g.c * z + g.d) = 0 := by
              -- `hw0` is exactly that up to rewriting
              rw [← neg_eq_iff_eq_neg.mpr hw0]
              field_simp [hden_g]
              rw [mul_comm] at hden_g
              field_simp [hden_g]
              ring

            exact this
          -- Expand hw1 and use hrel to kill the z-term, leaving comp.d = 0
          have hcompd0 : (comp f g).d = 0 := by
            dsimp [LinearFracTrans.comp]
            -- hw1 expands to (f.c*g.a + f.d*g.c)*z + (f.c*g.b + f.d*g.d) = 0
            -- use hrel = 0 to eliminate the z term
            have : (f.c * g.b + f.d * g.d) = 0 := by
              have h := hw1
              ring_nf at h
              -- h : (f.c * g.a + f.d * g.c) * z + (f.c * g.b + f.d * g.d) = 0
              -- Extract the relation f.c * g.a = -(f.d * g.c) from hrel

              have h_fcga_z : f.c * g.a * z = -(f.d * g.c) * z := by
              -- congrArg gives: (f.c*g.a) * z = (-(f.d*g.c)) * z
                simpa [mul_assoc] using congrArg (fun t : ℂ => t * z) h_fcga

              -- Rewrite the expanded equation and cancel the z-terms
              -- After rewriting, the z-terms become: (-(f.d*g.c))*z + (f.d*g.c)*z = 0
              -- and ring_nf will simplify it to the constant term = 0.
              rw [h_fcga_z] at h
              ring_nf at h
              -- Now h should be exactly: f.c * g.b + f.d * g.d = 0
              simpa [add_assoc, add_comm, add_left_comm] using h

            simpa using this
          exact hd_comp hcompd0

        rw [← apply_lft_coe (f := comp f g) (z := z)]
        rw [f_z_azbd (f := comp f g) (z := z) h_comp]
        norm_cast

        rw [(apply_lft_coe (f := g) (z := z)).symm]
        rw [f_value_when_c_nonzero (f := g) (z := z) hg hz]

        -- 1. Rewrite the argument of f to ↑w
        have h_arg : ((↑g.a * ↑z + ↑g.b) / (↑g.c * ↑z + ↑g.d) : EComplex) = (↑w : EComplex) := by
          -- Combine the EComplex operations into a single coercion
          -- We use hden_g to allow backwards coe_div
          have : ((↑g.a * ↑z + ↑g.b) / (↑g.c * ↑z + ↑g.d) : EComplex)
             = (↑ (g.a * z + g.b) / ↑(g.c * z + g.d) : EComplex) := by norm_cast
          rw [this]
          rw [← EComplex.coe_div _ _ hden_g]

        rw [h_arg]

        -- 2. Rewrite f w using the non-pole formula (using hw)
        rw [f_value_when_c_nonzero (f := f) (z := w) hf hw]

        -- 3. Verify denominator of f is non-zero (needed for coe_div)
        have hden_f : f.c * w + f.d ≠ 0 := by
          intro h0
          apply hw
          -- Solve f.c * w + f.d = 0  =>  w = -f.d/f.c
          rw [add_eq_zero_iff_eq_neg] at h0
          rw [eq_div_iff hf, mul_comm, ← neg_eq_iff_eq_neg]
          exact neg_eq_iff_eq_neg.mpr h0

        -- 4. use norm_cast to make it an equation in complex number
        norm_cast

        -- 5. Solve the algebra
        dsimp [w, comp]
        -- Clear denominators:
        -- hden_g (from g), hd_comp (from comp), hden_f (from f)
        field_simp [hden_g, hden_f, hd_comp']
        have : (f.c * (g.a * z + g.b) + f.d * (g.c * z + g.d)) =
              f.c * g.b + f.d *g.d := by
          -- 1. Expand the products
          ring_nf
          -- 2. Substitute f.c * g.a = -(f.d * g.c)
          simp only [h_fcga]
          -- 3. Simplify the result (cancellation)
          ring
        rw [this]
        field_simp [hd_comp']
        ring_nf

private lemma case222a {f g : LinearFracTrans} {z : Complex}
  (hf : f.c ≠ 0) (hg : g.c ≠ 0) (h_comp : (comp f g).c ≠ 0)
  (h_pole_g : g.c * z + g.d = 0)
    : (comp f g) z = f (g z) := by

  -- change ↑z to (some z) in the goal
  have : (↑ z : EComplex) = EComplex.some z := by exact rfl
  rw [this]

  have h_gcfd : g.c * f.d + f.c * g.a ≠ 0 := by
    -- Unfold the definition of comp.c
    dsimp [comp] at h_comp
    -- Rearrange terms to match the goal
    -- h_comp is f.c * g.a + f.d * g.c
    rw [add_comm, mul_comm g.c]
    exact h_comp

  have hz : z = -g.d / g.c := by
    rw [add_eq_zero_iff_eq_neg] at h_pole_g
    rw [eq_div_iff hg, mul_comm, ← neg_eq_iff_eq_neg]
    exact neg_eq_iff_eq_neg.mpr h_pole_g

  -- RHS: g(z) = ∞, so f(g(z)) = f(∞) = f.a / f.c
  have hR : f (g (EComplex.some z)) = (f.a / f.c : ℂ∞) := by
      rw [hz]
      rw [apply]
      -- simplify g(-d/c) -> ∞
      simp [hg]
      rw [@f_infty_a_div_c f hf]

  -- LHS: Check if z is pole of comp.
  -- If z were pole of comp, then comp.c(-d/c) + comp.d = 0
  -- We check the denominator value:
  have h_denom_comp : (comp f g).c * z + (comp f g).d ≠ 0 := by
    rw [hz]
    dsimp [comp]
    field_simp [hg]
    -- reduces to f.c * (-det(g))
    intro h
    have h_det : f.c * -(g.a * g.d - g.b * g.c) = 0 := by
      ring_nf at h
      have : -(f.c * g.a * g.d) + f.c * g.c * g.b
             =  f.c * -(g.a * g.d - g.b * g.c) := by
        ring
      rw [← this]
      exact h

    have h_det_g_nz : -(g.a * g.d - g.b * g.c) ≠ 0 := by
      rw [neg_ne_zero]
      exact g.determinant_ne_zero

    exact mul_ne_zero hf h_det_g_nz h_det

  -- So LHS is finite
  have h_z_not_pole_comp
    : z ≠ -(comp f g).d / (comp f g).c := by
    intro h; apply h_denom_comp
    rw [h]; field_simp [h_comp]; ring

  rw [hR]
  rw [← apply_lft_coe (comp f g) z]
  rw [@f_value_when_c_nonzero (comp f g)
       _ h_comp h_z_not_pole_comp]

  -- Algebra
  rw [hz]
  norm_cast
  dsimp [comp]

  have h_denom_val_ne_zero
    : ((f.c * g.a + f.d * g.c) * (-g.d / g.c)
      + (f.c * g.b + f.d * g.d)) ≠ 0 := by
    convert h_denom_comp using 1
    dsimp [comp]
    rw [hz]

  -- 2. Use that proof to push coercion inside division
  have : (↑((f.a * g.a + f.b * g.c) * (-g.d / g.c)
    + (f.a * g.b + f.b * g.d)) / ↑((f.c * g.a + f.d * g.c)
    * (-g.d / g.c) + (f.c * g.b + f.d * g.d)) : EComplex)
    = ↑(((f.a * g.a + f.b * g.c) * (-g.d / g.c)
    + (f.a * g.b + f.b * g.d)) / ((f.c * g.a + f.d * g.c)
    * (-g.d / g.c) + (f.c * g.b + f.d * g.d))) := by
      rw [← EComplex.coe_div _ _ h_denom_val_ne_zero]

  rw [this]
  norm_cast

  -- 3. Prove the determinant helper
  have clear_det : -(g.d * (g.a * f.c + g.c * f.d))
                 + g.c * (g.b * f.c + g.d * f.d) ≠ 0 := by
    have : -(g.d * (g.a * f.c + g.c * f.d))
           + g.c * (g.b * f.c + g.d * f.d)
            = f.c * -(g.a * g.d - g.b * g.c) := by ring
    rw [this]
    exact mul_ne_zero hf
      (neg_ne_zero.mpr g.determinant_ne_zero)

  have h_z_not_pole_comp: z ≠ -(comp f g).d /(comp f g).c
    := by
    intro h_eq
    -- Substitute z = -g.d / g.c into the equation
    rw [hz] at h_eq

    -- Expand 'comp' and clear denominators
    dsimp [comp] at h_eq
    field_simp [hg, h_comp, h_gcfd] at h_eq

    -- Simplify the equation.
    -- The terms involving f.d will cancel out,
    -- leaving f.c * -det(g) = 0
    have h_contra : f.c * -(g.a * g.d - g.b * g.c) = 0
      := by
      -- ring_nf on h_eq moves terms around.
      -- Show h_eq implies the determinant relation.
      have : f.c * g.a + g.c * f.d ≠ 0 := by
        rw [add_comm]
        exact h_gcfd

      field_simp [this] at h_eq
      ring_nf at h_eq
      have h_sub : (-(g.d * f.c * g.a) - g.d * g.c * f.d)
        - (-(g.d * g.c * f.d) - f.c * g.c * g.b) = 0 := by
        rw [h_eq, sub_self]
      have : -(g.d * f.c * g.a) - g.d * g.c * f.d
          - (-(g.d * g.c * f.d) - f.c * g.c * g.b)
          = f.c * -(g.a * g.d - g.b * g.c) := by ring
      rw [← this]
      assumption

    -- Derive contradiction
    -- We know f.c ≠ 0 and det(g) ≠ 0
    have h_det_nz : -(g.a * g.d - g.b * g.c) ≠ 0 := by
      rw [neg_ne_zero]
      exact g.determinant_ne_zero
    exact mul_ne_zero hf h_det_nz h_contra

  -- 4. Solve the algebra
  --    Pass h_denom_val_ne_zero so field_simp knows
  --    it can multiply by the denominator
  field_simp [hf, hg, h_denom_val_ne_zero]
  ring

private lemma case222b
  {f g : LinearFracTrans} {z : Complex}
  (hf : f.c ≠ 0) (hg : g.c ≠ 0)
  (h_comp : (comp f g).c ≠ 0)
  (h_not_pole_g : g.c * z + g.d ≠ 0)
    : (comp f g) z = f (g z) := by

  have h_gcfd : g.c * f.d + f.c * g.a ≠ 0 := by
    -- Unfold the definition of comp.c
    dsimp [comp] at h_comp
    -- Rearrange terms to match the goal
    -- h_comp is f.c * g.a + f.d * g.c
    rw [add_comm, mul_comm g.c]
    exact h_comp

  have hz : z ≠ -g.d / g.c := by
    intro h
    apply h_not_pole_g
    rw [h]
    field_simp [hg]
    ring

  -- Let w = g(z)
  let w : ℂ := (g.a * z + g.b) / (g.c * z + g.d)

  -- Check if w is a pole of f (i.e., z is a pole of comp)
  by_cases h_pole_comp
    : (comp f g).c * z + (comp f g).d = 0
  · -- Case: z is a pole of comp -> LHS = ∞
    have hz_pole : z = -(comp f g).d / (comp f g).c := by
        rw [add_eq_zero_iff_eq_neg] at h_pole_comp
        rw [eq_div_iff h_comp,mul_comm,←neg_eq_iff_eq_neg]
        exact neg_eq_iff_eq_neg.mpr h_pole_comp

    -- LHS = ∞
    --rw [← apply_lft_coe (comp f g) z]
    rw [hz_pole]
    -- Apply the theorem for the function (comp f g)
    have : (↑(-(f.comp g).d / (f.comp g).c) : EComplex) =
      (-↑ (f.comp g).d / ↑(f.comp g).c) := by norm_cast
    rw [this]
    rw [f_neg_d_div_c_infty h_comp]

    -- RHS: We claim w is the pole of f
    have hw_pole : f.c * w + f.d = 0 := by
      dsimp [comp] at h_pole_comp
      -- Substitute w definition
      have : f.c * ((g.a*z+g.b)/(g.c*z+g.d)) + f.d = 0
        := by
        field_simp [h_not_pole_g]
        have : z * g.c + g.d ≠ 0 := by
          rw [mul_comm]
          exact h_not_pole_g
        -- Numerator matches pole condition
        field_simp [this]
        ring_nf
        have : f.c * g.a * z + f.c * g.b
          + z * g.c * f.d + g.d * f.d
          = (f.c * g.a + f.d * g.c) * z
          + (f.c * g.b + f.d * g.d) := by ring
        rw [this]
        exact h_pole_comp
      exact this

    have hw : w = -f.d / f.c := by
      rw [add_eq_zero_iff_eq_neg] at hw_pole
      rw [eq_div_iff hf, mul_comm, ← neg_eq_iff_eq_neg]
      exact neg_eq_iff_eq_neg.mpr hw_pole

    -- RHS = f(w) = ∞
    have hR:
      f.apply (g.apply (-↑(f.comp g).d / ↑(f.comp g).c))
      = none := by
      -- rw [← apply_lft_coe g]
      have h_z_pole_neq : -(comp f g).d / (comp f g).c
          ≠ -g.d / g.c := by
        intro h
        -- Expand the equality
        dsimp [comp] at h
        field_simp [hg, h_comp] at h
        -- Reduce using ring algebra.
        -- We will derive f.c * -(g.a*g.d - g.b*g.c) = 0
        ring_nf at h
        have h_contra : f.c * -(g.a * g.d - g.b * g.c) = 0
          := by
          have : f.c * g.a + f.d * g.c ≠ 0 := by
            have : f.c * g.a + f.d * g.c
                   = g.c * f.d + f.c * g.a := by ring
            rw [this]
            assumption
          field_simp [this] at h
          have : f.c * g.a + g.c * f.d ≠ 0 := by
            have : f.c * g.a + g.c * f.d
                   = g.c * f.d + f.c * g.a := by ring
            rw [this]
            assumption
          field_simp [this] at h
          have h_sub : g.c * (-(f.c * g.b) - f.d * g.d)
                      + (g.d * (f.c * g.a + g.c * f.d))
            = 0 := by exact eq_neg_iff_add_eq_zero.mp h

          -- normalize both sides
          ring_nf at h_sub
          have h_neg : (g.c * f.c * g.b)
              - f.c * g.d * g.a = 0 := by
            rw [← neg_eq_zero]
            ring_nf
            assumption

          ring_nf at h_neg
          ring_nf
          have : g.c * f.c * g.b - f.c * g.d * g.a
                = -(f.c * g.a * g.d) + f.c * g.b * g.c
                  := by ring
          rw [← this]
          exact h_neg

        -- Contradiction
        have h_det_nz : -(g.a * g.d - g.b * g.c) ≠ 0 := by
          rw [neg_ne_zero]
          exact g.determinant_ne_zero

        exact mul_ne_zero hf h_det_nz h_contra

      have : (↑(-(f.comp g).d / (f.comp g).c) : EComplex)
           = (-↑(f.comp g).d / ↑(f.comp g).c)
        := by norm_cast
      rw [← this]
      rw [@f_value_when_c_nonzero g _ hg h_z_pole_neq]

      have h_pole_f :
        ((↑g.a * ↑(-(f.comp g).d / (f.comp g).c) + ↑g.b)
        / (↑g.c * ↑(-(f.comp g).d / (f.comp g).c) + ↑g.d))
        = (-f.d/f.c : EComplex) := by
        have h_denom_g_ne0 :
          g.c * (-(comp f g).d / (comp f g).c) + g.d ≠ 0
          := by
            intro h
            apply h_z_pole_neq
            rw [add_eq_zero_iff_eq_neg] at h
            rw [eq_div_iff hg, mul_comm,←neg_eq_iff_eq_neg]
            exact neg_eq_iff_eq_neg.mpr h

        have : ((↑g.c * ↑(-(f.comp g).d / (f.comp g).c)
               + ↑g.d) : EComplex)
            = ↑(g.c * (-(f.comp g).d / (f.comp g).c) + g.d)
            := by norm_cast
        rw [this]
        have :((↑g.a*↑(-(f.comp g).d/(f.comp g).c) + ↑g.b)
          : EComplex)
          = ↑(g.a * (-(f.comp g).d / (f.comp g).c) + g.b)
          := by norm_cast
        rw [this]
        rw [← EComplex.coe_div _ _ h_denom_g_ne0]
        norm_cast

        -- 2. Solve the algebra in ℂ
        dsimp [comp]
        field_simp [hf, hg, h_comp, h_denom_g_ne0]
        have : g.a * f.c + f.d * g.c ≠ 0 := by
          have : g.a*f.c + f.d*g.c = g.c*f.d + f.c*g.a
                 := by ring
          rwa [this]
        field_simp [this]
        have : f.c * g.a + f.d * g.c ≠ 0 := by
          have : f.c * g.a + f.d * g.c = g.c * f.d
                 + f.c * g.a := by ring
          rwa [this]
        field_simp [this]

        have : -((f.c * g.b + f.d * g.d) * g.c)
              + g.d * (f.c * g.a + f.d * g.c) ≠ 0 := by
          ring_nf
          have : -(f.c * g.b * g.c) + f.c * g.d * g.a
                 = f.c *(g.a*g.d - g.b*g.c) := by ring
          rw [this]
          have : g.a*g.d - g.b*g.c≠ 0
            := by exact g.determinant_ne_zero
          exact mul_ne_zero hf this

        field_simp [this]
        ring

      -- 3. Use the fact that w is the pole of f (hw)
      rw [h_pole_f]

      -- 4. Apply the pole property of f
      rw [f_neg_d_div_c_infty hf]

    rw [hR]

  · -- Case: z is NOT a pole of comp -> LHS is finite
    have hz_not_pole_comp : z ≠ -(comp f g).d /(comp f g).c
      := by
      intro h
      apply h_pole_comp
      rw [h]
      field_simp [h_comp]
      ring

    -- w is not a pole of f
    have hw_not_pole : f.c * w + f.d ≠ 0 := by
      intro h
      apply h_pole_comp
      dsimp [comp]
      dsimp [w] at h
      field_simp [h_not_pole_g] at h

      -- Now h is exactly the expansion of
      -- comp.c * z + comp.d = 0
      -- We use ring_nf to align the terms
      have h_expanded :
        f.c * (g.a * z + g.b) + f.d * (g.c * z + g.d) = 0
        := by
        have : z * g.c + g.d ≠ 0 := by
          have : z * g.c + g.d = g.c * z + g.d:= by ring
          rwa [this]
        field_simp [this] at h
        ring_nf at h
        have h_sub : f.c * g.a * z + f.c * g.b
             + z * g.c * f.d + g.d * f.d = 0
          := by exact h
        ring_nf at h_sub
        ring_nf
        have : f.c * g.a * z + f.c * g.b
               + z * g.c * f.d + f.d * g.d
            = f.c * g.a * z + f.c * g.b
              + z * f.d * g.c + f.d * g.d := by ring
        rw [← this]
        assumption

      -- Expand the goal
      ring_nf
      -- Expand the hypothesis
      ring_nf at h_expanded

      have : f.c * g.a * z + f.c * g.b
           + z * f.d * g.c + f.d * g.d
        = f.c * g.a * z + f.c * g.b
        + f.d * g.c * z + f.d * g.d := by ring
      rw [← this]

      exact h_expanded

    have hz_not_pole_comp : z ≠ -(comp f g).d/(comp f g).c
      := by
      intro h
      apply h_pole_comp
      rw [h]
      field_simp [h_comp]
      ring

    have hw : w ≠ -f.d / f.c := by
      intro h
      apply hw_not_pole
      rw [h]
      field_simp [hf]
      ring

    -- Prove equality of finite values
    --rw [← apply_lft_coe (comp f g) z]
    rw [@f_value_when_c_nonzero (comp f g)
      _ h_comp hz_not_pole_comp]

    rw [@f_value_when_c_nonzero g _ hg hz]

    -- 1. Identify the complex argument on RHS with w
    have h_arg : ((↑g.a * ↑z + ↑g.b) / (↑g.c * ↑z + ↑g.d)
        : EComplex) = ↑w := by
      -- Merge the arithmetic into a single coercion
      have :
        ((↑g.a * ↑z + ↑g.b) / (↑g.c * ↑z + ↑g.d):EComplex)
          = (↑(g.a * z + g.b) / ↑(g.c * z + g.d):EComplex)
        := by norm_cast
      rw [this]
      rw [← EComplex.coe_div _ _ h_not_pole_g]

    -- 2. Substitute into the goal
    rw [h_arg]

    -- 3. Apply the value lemma for f
    rw [@f_value_when_c_nonzero f _ hf hw]

    -- 4. Solve the Algebra
    norm_cast
    dsimp [w, comp]

    -- Clear all denominators.
    field_simp [h_not_pole_g, hw_not_pole, h_pole_comp]
    ring

private lemma case222
  {f g : LinearFracTrans} {z : EComplex}
  (hf : f.c ≠ 0) (hg : g.c ≠ 0) (h_comp : (comp f g).c ≠ 0)
    : (comp f g) z = f (g z) := by
  cases z with
  | none =>
    -- Case z = ∞
    -- RHS: g(∞) = g.a / g.c
    -- Since h_comp : f.c * g.a + f.d * g.c ≠ 0,
    -- g(∞) is NOT the pole of f.
    have h_g_inf_not_pole : (g.a / g.c) ≠ -f.d / f.c := by
      intro h
      have h_eq : f.c * (g.a / g.c) + f.d = 0 := by
        rw [h]; field_simp [hf]; ring
      -- Multiply by g.c to get comp.c
      have : (comp f g).c = 0 := by
        dsimp [comp]
        field_simp [hg] at h_eq
        ring_nf at h_eq
        have:f.c * g.a + f.d * g.c = f.c * g.a + g.c * f.d
           := by ring
        rw [this]
        exact h_eq
      exact h_comp this
    -- Rewrite both sides to finite complex values
    rw [f_infty_a_div_c h_comp]
    rw [f_infty_a_div_c hg]
    -- Goal is now: ↑((f.comp g).a) / ↑((f.comp g).c)
    -- = f.apply (↑g.a / ↑g.c)
    -- 1. Simplify the argument on RHS
    have h_arg :
      (↑g.a / ↑g.c : EComplex) = (↑(g.a / g.c) : EComplex)
      := by norm_cast
    rw [h_arg]
    -- 3. Now the rewrite matches perfectly
    rw [f_value_when_c_nonzero hf h_g_inf_not_pole]
    dsimp [comp]
     -- Algebra
    norm_cast
    have : (↑(f.a * g.a + f.b * g.c)
           / ↑(f.c * g.a + f.d * g.c) : EComplex)
           =  ↑((f.a * g.a + f.b * g.c)
           / (f.c * g.a + f.d * g.c) ) := by
      have h_comp_c_ne_zero :
          f.c * g.a + f.d * g.c ≠ 0 := by
        dsimp [comp] at h_comp
        exact h_comp
      rw [← EComplex.coe_div _ _ h_comp_c_ne_zero]
    rw [this]
    have :
      (↑(f.a * (g.a / g.c) + f.b)
      / ↑(f.c * (g.a / g.c) + f.d) : EComplex)
      = ↑((f.a * (g.a / g.c) + f.b)
      / (f.c * (g.a / g.c) + f.d))
      := by
      have h_denom_f_ne_zero :
          f.c * (g.a / g.c) + f.d ≠ 0 := by
        intro h
        have h_eq : g.a / g.c = -f.d / f.c := by
          rw [add_eq_zero_iff_eq_neg] at h
          rw [eq_div_iff hf, mul_comm,←neg_eq_iff_eq_neg]
          exact neg_eq_iff_eq_neg.mpr h
        exact h_g_inf_not_pole h_eq
      rw [← EComplex.coe_div _ _ h_denom_f_ne_zero]
    rw [this]
    norm_cast   -- reduce to finite complex number
    field_simp [hf, hg, h_comp]
  | some z =>
    -- Case z is finite
    -- Split on whether z is the pole of g
    have h_gcfd : g.c * f.d + f.c * g.a ≠ 0 := by
      -- Unfold the definition of comp.c
      dsimp [comp] at h_comp
      -- Rearrange terms to match the goal
      -- h_comp is f.c * g.a + f.d * g.c
      rw [add_comm, mul_comm g.c]
      exact h_comp
    by_cases h_pole_g : g.c * z + g.d = 0
    · -- SubCase 1:
      --    z is the pole of g
      exact case222a hf hg h_comp h_pole_g
    · -- Subcase 2
      --  z is NOT the pole of g
      exact case222b hf hg h_comp h_pole_g


/--
  The linear fractional transformation with multplication
  defined as in matrix is a group action on the Riemann
  sphere.

  we divide into cases based on whether f.c and g.c are
  zero or not, and use the preceeding helper lemmas
  to resolve the various cases.
-/
@[simp]
theorem comp_apply (f g : LinearFracTrans) (z : EComplex)
  : (comp f g) z = f (g z) := by
  by_cases hf : f.c = 0  -- Split on whether f.c is zero
  -- BRANCH 1: f.c = 0
  · by_cases hg : g.c = 0 -- Split on whether g.c is zero
    -- Branch 1.1: f.c = 0, g.c = 0
    · exact case11 hf hg
    -- Branch 1.2: f.c = 0, g.c ≠ 0
    · have h_comp_c : (comp f g).c ≠ 0 := by
        exact comp_f_g_not_affine1 hf hg
      by_cases h : g.c * z + g.d = 0
      · -- Case 1.2.1: f.c=0, g.c≠0, g.c * z + g.d = 0
        exact case121 hf hg h_comp_c h
      · -- Case 1.2.2: f.c=0, g.c≠0, g.c * z + g.d ≠ 0
        exact case122 hf hg h_comp_c h
  -- BRANCH 2: f.c ≠ 0
  · -- Split on g.c
    by_cases hg : g.c = 0
    -- Branch 2.1: f.c ≠ 0, g.c = 0
    · have h_comp_c : (comp f g).c ≠ 0
        := comp_f_g_not_affine2 hf hg
      by_cases h :
        f.c * g.a * z + (f.c * g.b + f.d * g.d) = 0
      · -- 2.1.1: f.c≠0, g.c=0, z is a pole of f∘g
        exact case211 hf hg h_comp_c h
      · -- 2.1.2: f.c≠0, g.c=0, z is not a pole of f∘g
        exact case212 hf hg h_comp_c h
    -- Branch 2.2: f.c ≠ 0, g.c ≠ 0
    · -- Split on (comp f g).c
      by_cases h_comp : (comp f g).c = 0
      · -- 2.2.1: f.c≠0, g.c≠0, (comp).c=0
        exact case221 hf hg h_comp
      · -- 2.2.2: f.c≠0, g.c≠0, (comp).c≠0
        exact case222 hf hg h_comp

end LFTComposition







section GroupAction


/-- The identity linear fractional transformation is
    the identity element for composition
-/
lemma lft_one_mul (f : LinearFracTrans)
  : comp id f = f := by
  unfold comp
  ext <;>
  · simp [LinearFracTrans.id]

lemma lft_mul_one (f : LinearFracTrans)
    : comp f (LinearFracTrans.id) = f := by
 unfold comp
 ext <;>
 · simp [LinearFracTrans.id]

/--
  Associative property for composition of LFT.

  This is essentially the same as the associativity
  of matrix multiplication.
-/
lemma lft_mul_assoc (f g h : LinearFracTrans)
  : (comp (comp f g) h) = (comp f (comp g h)) := by
 ext <;>
 · unfold comp
   simp_all
   ring


/--  #### Theorem 2.3.6
  The inverse of a linear fractional transformation
  is a linear fractional transformation
-/
def inv (f : LinearFracTrans)
    : LinearFracTrans where
  a := f.d/(f.a * f.d - f.b * f.c)
  b := -f.b/(f.a * f.d - f.b * f.c)
  c := -f.c/(f.a * f.d - f.b * f.c)
  d := f.a/(f.a * f.d - f.b * f.c)
  determinant_ne_zero := by
    have h : (f.d * f.a - f.b * f.c)⁻¹ ^ 2 * (f.d * f.a)
      - f.b * f.c * (f.d*f.a - f.b*f.c)⁻¹ ^ 2 =
      (f.d*f.a - f.b*f.c)*(f.d*f.a - f.b*f.c)⁻¹ ^ 2
      := by ring
    ring_nf
    rw [mul_comm, h]
    simp only [inv_pow, ne_eq, mul_eq_zero, inv_eq_zero,
      OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, or_self]
    rw [mul_comm]
    exact f.determinant_ne_zero


/--
    The inverse of a linear fractional transformation f,
    composed with f, gives the identity transformation
-/
lemma lft_mul_left_inv (f : LinearFracTrans)
   : comp (inv f) f = id := by
  unfold inv
  ext
  · unfold comp
    simp
    calc
    _ = (f.d * f.a + (-f.b) * f.c)/(f.a * f.d - f.b * f.c)
          := by ring
    _ = (f.a * f.d  -f.b * f.c)/(f.a * f.d - f.b * f.c)
          := by ring
    _ = 1 := by
      apply div_self
      exact f.determinant_ne_zero
  · unfold comp
    simp
    calc
      _ = (f.d * f.b -f.d * f.b) / (f.a * f.d - f.b * f.c)
          := by ring
      _ = 0 := by ring
  · unfold comp
    simp
    calc
    _ = (f.a * f.c -f.a * f.c) / (f.a * f.d - f.b * f.c)
         := by ring
    _ = 0 := by ring
  · unfold comp
    simp
    calc
    _ = (f.a * f.d  -f.b * f.c) / (f.a * f.d - f.b * f.c)
        := by ring
    _ = 1 := by
      apply div_self
      exact f.determinant_ne_zero


lemma lft_mul_right_inv (f : LinearFracTrans)
   : comp f (inv f)= id := by
  unfold inv
  ext
  · unfold comp
    simp
    calc
    _ = (f.d * f.a + (-f.b) * f.c) / (f.a * f.d - f.b * f.c)
        := by ring
    _ = (f.a * f.d  -f.b * f.c) / (f.a * f.d - f.b * f.c)
        := by ring
    _ = 1 := by
      apply div_self
      exact f.determinant_ne_zero
  · unfold comp
    simp
    calc
      _ = (f.d * f.b -f.d * f.b) / (f.a * f.d - f.b * f.c)
           := by ring
      _ = 0 := by ring
  · unfold comp
    simp
    calc
    _ = (f.a * f.c -f.a * f.c) / (f.a * f.d - f.b * f.c)
         := by ring
    _ = 0 := by ring
  · unfold comp
    simp
    calc
    _ = (f.a * f.d  -f.b * f.c) / (f.a * f.d - f.b * f.c)
         := by ring
    _ = 1 := by
      apply div_self
      exact f.determinant_ne_zero


/-- The set of linear fractional transformations forms
    a group under composition
-/
instance : Group (LinearFracTrans) where
  mul := comp
  mul_assoc := by
    intro f g h
    dsimp [·*·]
    exact lft_mul_assoc f g h
  one := LinearFracTrans.id
  one_mul := by
    dsimp [·*·]
    apply lft_one_mul
  mul_one := by
    dsimp [·*·]
    apply lft_mul_one
  inv := LinearFracTrans.inv
  inv_mul_cancel := by
    dsimp [·*·]
    apply lft_mul_left_inv


/--
A wrapper lemma: (f * g) • z = f • (g • z)
-/
@[simp]
theorem mul_apply (f g : LinearFracTrans) (z : EComplex) :
    (f * g) z = f (g z) := by
  change (comp f g) z = f (g z)
  exact comp_apply f g z

/--
Prove identity acts as identity
-/
@[simp]
theorem one_apply (z : EComplex) :
    id z = z := by
  -- proof depends on your definition of apply
  cases z with
  | none =>
      simp [LinearFracTrans.id]
  | some z =>
      exact id_apply (Option.some z)

/--  #### Theorem 2.3.7
    Register a group action
    The group of LFT actions on EComplex as a
    multiplicative group action.
-/
instance instMulActionEComplex :
    MulAction LinearFracTrans EComplex where
  smul f z := f z
  one_smul := by
    intro z
    exact one_apply z
  mul_smul := by
    intro f g z
    exact mul_apply f g z

/--
  Add a simp lemma for scalar action notation
-/
@[simp]
theorem smul_eq_apply (f : LinearFracTrans) (z : EComplex) :
    f • z = f z := rfl

-- Using the previous theorem `smul_eq_apply`
-- we can test scalar multiplication
-- with the following examples.
example (f g : LinearFracTrans) (z : EComplex) :
    (f * g) • z = f • (g • z) := by
  simp

example (f g : LinearFracTrans) (z : EComplex) :
    (f * g) z = f (g z) := by
  simp

-- Example of using group action theorem from Mathlib
example (f : LinearFracTrans) (z : EComplex) :
  f⁻¹ • f • z = z := by
  -- Distribute action: (f * f⁻¹) • z  ->  f • (f⁻¹ • z)
  rw [← mul_smul]
  -- Simplify f * f⁻¹ to 1 using the standard Group theorem
  rw [inv_mul_cancel]
  -- Simplify 1 • z to z
  rw [one_smul]

-- Example of using group action theorem from Mathlib
example (z : EComplex) :
  id • z = z := by
  apply one_smul

end GroupAction



noncomputable section LFT_CircleLine

/-
 ## Action ofFractional Linear transformation
 ## on circle and line
-/

/--  Algebraic data of a generalized circle

In the complex plane, any circle or line can be
represented by the real equation

A |z|^2 + (conj B) * z + B * (conj z) + C = 0

or, equivalently

A |z|^2 + 2 Re ( (conj B)(z)) + C = 0.

The coefficients A and C are real constants.
The coefficients B is a complex constant.
Subject to the condition that A * C < |B|^2, which
ensures that the circle has a real and positive radius
and is not just a point or empty.
-/
structure Cirline where
  A : ℝ
  B : ℂ
  C : ℝ
  h_nondeg : A * C < Complex.normSq B

open Cirline

/-- The points in the extended complex plane belonging
to the circline -/
def Cirline.set (cir : Cirline) : Set EComplex :=
  {z : EComplex |
    match z with
    | EComplex.some c => cir.A * Complex.normSq c
        + 2 * (cir.B.re * c.re + cir.B.im * c.im)
        + cir.C = 0
    | none   => cir.A = 0}

/-- A set is a circline if it is generated by
  some Cirline data -/
def isCirline (S : Set EComplex) : Prop :=
  ∃ cir : Cirline, S = cir.set

namespace LFT_Cirline

-- define the notation for complex conjugate
notation "conj" => (starRingEnd ℂ)


/-! ### Step 1: The Three Generators -/

/-- Translation z ↦ z + t preserves circlines. -/
lemma translation_maps_cirline (S : Set EComplex)
    (t : ℂ) (h : isCirline S) :
    isCirline ((fun z => z + t) '' S) := by
  -- Extract original coefficients
  rcases h with ⟨⟨A, B, C, h_nondeg⟩, rfl⟩

  -- The witnesses for the new coeff. after translation
  let A' := A
  let B' := B - A * t
  let C' := A * Complex.normSq t - 2*(conj B * t).re + C

  -- Algebraic identity for the nondegeneracy condition.
  have h_disc :
    A' * C' - Complex.normSq B' =
    A * C - Complex.normSq B := by
      simp [A', B', C', Complex.normSq]
      ring

  have h_nondeg' : A' * C' < Complex.normSq B' := by
    have hneg : A' * C' - Complex.normSq B' < 0 := by
      rw [h_disc]
      linarith
    linarith

  -- Forward algebraic identity:
  -- the new equation at `c + t` equals the old equation at `c`.
  have h_forward : ∀ c : ℂ,
      A' * Complex.normSq (c + t)
        + 2 * (B'.re * (c + t).re + B'.im * (c + t).im)
        + C'
      =
      A * Complex.normSq c
        + 2 * (B.re * c.re + B.im * c.im)
        + C := by
    intro c ; simp[ A', B', C', Complex.normSq] ; ring

  -- Backward algebraic identity:
  -- the old equation at `c - t` equals
  -- the new equation at `c`.
  have h_backward : ∀ c : ℂ,
      A * Complex.normSq (c - t)
        + 2 * (B.re * (c - t).re + B.im * (c - t).im)
        + C
      =
      A' * Complex.normSq c
        + 2 * (B'.re * c.re + B'.im * c.im)
        + C' := by
    intro c; simp[ A', B', C', Complex.normSq]; ring

  refine ⟨⟨A', B', C', h_nondeg'⟩, ?_⟩
  · ext z
    constructor
    · -- Forward inclusion.
      rintro ⟨w, hw, rfl⟩
      cases w with
      | none =>
          -- Infinity is fixed by translation.
          -- Membership at infinity means `A = 0`.
          simpa [Cirline.set, A'] using hw
      | some c =>
          have hw' :
            A' * Complex.normSq (c + t)
            + 2 * (B'.re * (c + t).re + B'.im * (c + t).im)
            + C' = 0 := by
              rw [h_forward c]
              simpa [Cirline.set] using hw
          change (EComplex.some (c + t) : EComplex) ∈
            ({ A := A', B := B', C := C', h_nondeg
              := h_nondeg' } : Cirline).set
          simpa [Cirline.set] using hw'

    · -- Reverse inclusion.
      intro hz
      cases z with
      | none =>
          refine ⟨none, ?_, ?_⟩
          · simpa [Cirline.set, A'] using hz
          · simp
      | some c =>
          refine ⟨EComplex.some (c - t), ?_, ?_⟩
          · have hz' :
                A * Complex.normSq (c - t) + 2 *
                (B.re * (c - t).re + B.im * (c - t).im)
                  + C = 0 := by
              rw [h_backward c]
              simpa [Cirline.set] using hz
            simpa [Cirline.set] using hz'
          · simp
            change (EComplex.some (t + (c - t)) : EComplex)
              = EComplex.some c
            congr
            ring


/-- Scaling/Rotation z ↦ s * z preserves circlines. -/
lemma scaling_maps_cirline (S : Set EComplex)
  (s : ℂ) (hs : s ≠ 0) (h : isCirline S) :
    isCirline ((fun z => s * z) '' S) := by
  rcases h with ⟨⟨ A, B, C, h_nondeg⟩ , rfl⟩

  -- The witnesses for the new coefficients after scaling:
  let A' := A
  let B' := B * s
  let C' := C * Complex.normSq s

  -- In fact it is positive.
  have hs_norm_pos : 0 < Complex.normSq s := by
    have hs_norm_nonneg : 0 ≤ Complex.normSq s := by
      simp [Complex.normSq]
      nlinarith [mul_self_nonneg s.re,
        mul_self_nonneg s.im]
    exact lt_of_le_of_ne hs_norm_nonneg (by
      intro h0
       -- `Complex.normSq s ≠ 0` because `s ≠ 0`
      exact hs (Complex.normSq_eq_zero.mp h0.symm))

  -- Algebraic identity for the discriminant condition.
  have h_disc :
      A' * C' - Complex.normSq B' = (A * C -
      Complex.normSq B) * Complex.normSq s := by
    simp [A', B', C', Complex.normSq]
    ring

  have h_nondeg' : A' * C' < Complex.normSq B' := by
    have hneg : A * C - Complex.normSq B < 0 := by
      linarith
    have hprod :
      (A * C - Complex.normSq B) * Complex.normSq s < 0
      := by
        exact mul_neg_of_neg_of_pos hneg hs_norm_pos
    have hdiff : A' * C' - Complex.normSq B' < 0 := by
      rw [h_disc]
      exact hprod
    linarith

  -- Forward algebraic identity:
  -- the new equation at `s * c` is the old
  -- equation at `c`, multiplied by `|s|²`.
  have h_forward : ∀ c : ℂ,
      A' * Complex.normSq (s * c)
        + 2 * (B'.re * (s * c).re + B'.im * (s * c).im)
        + C'
      =
      (A * Complex.normSq c
        + 2 * (B.re * c.re + B.im * c.im)
        + C) * Complex.normSq s := by
    intro c
    simp [A', B', C', Complex.normSq]
    ring

  refine ⟨⟨A', B', C', h_nondeg'⟩, ?_⟩

  ext z
  constructor
  · -- Forward inclusion.
    rintro ⟨w, hw, rfl⟩
    cases w with
    | none =>
        -- Infinity is fixed by nonzero scaling.
        simpa [Cirline.set] using hw
    | some c =>
        have hw0 :
            A * Complex.normSq c
              + 2 * (B.re * c.re + B.im * c.im)
              + C = 0 := by
          simpa [Cirline.set] using hw

        have hw' :
            A' * Complex.normSq (s * c)
              + 2 * (B'.re * (s * c).re + B'.im * (s * c).im)
              + C' = 0 := by
          rw [h_forward c]
          simp [hw0]

        change (EComplex.some (s * c) : EComplex) ∈
          ({ A := A', B := B', C := C', h_nondeg
            := h_nondeg'} : Cirline).set
        simpa [Cirline.set] using hw'

  · -- Reverse inclusion.
    intro hz
    cases z with
    | none =>
        refine ⟨none, ?_, ?_⟩
        · simpa [Cirline.set, A'] using hz
        · simp only [mul_comm_ecomplex,infinity_mul_finite]

    | some c =>
        -- The preimage of `c` is `s⁻¹ * c`.
        refine ⟨EComplex.some (s⁻¹ * c), ?_, ?_⟩

        · have hz0 :
              A' * Complex.normSq c
                + 2 * (B'.re * c.re + B'.im * c.im)
                + C' = 0 := by
            simpa [Cirline.set] using hz

          have hsc : s * (s⁻¹ * c) = c := by
            rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

          have hzscale :
              A' * Complex.normSq (s * (s⁻¹ * c))
                + 2 * (B'.re * (s * (s⁻¹ * c)).re
                    + B'.im * (s * (s⁻¹ * c)).im)
                + C' = 0 := by
            simpa [hsc] using hz0

          have hmul :
              (A * Complex.normSq (s⁻¹ * c)
                + 2 * (B.re * (s⁻¹ * c).re
                    + B.im * (s⁻¹ * c).im)
                + C) * Complex.normSq s = 0 := by
            rw [← h_forward (s⁻¹ * c)]
            exact hzscale

          have hz' :
              A * Complex.normSq (s⁻¹ * c)
                + 2 * (B.re * (s⁻¹ * c).re
                    + B.im * (s⁻¹ * c).im)
                + C = 0 := by
            rcases mul_eq_zero.mp hmul with hleft | hright
            · exact hleft
            · exact False.elim
                (hs (Complex.normSq_eq_zero.mp hright))
          simpa [Cirline.set] using hz'

        · change (EComplex.some (s * (s⁻¹ * c)) : EComplex)
            = EComplex.some c
          congr 1
          rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]



/--  #### Theorem 2.1.1
  Inversion z ↦ 1/z preserves circlines.
-/
lemma inversion_maps_cirline
  (S : Set EComplex) (h : isCirline S) :
    isCirline ((fun z => z⁻¹) '' S) := by
  rcases h with ⟨⟨ A, B, C, h_nondeg⟩ , rfl⟩

  -- Witnesses for the new coefficients after inversion:
  -- The equation A|z|² + 2Re(B'z) + C = 0 multiplied by
  -- |w|² becomes C|w|² + 2Re(B'w) + A = 0
  let A' := C
  let B' := conj B
  let C' := A

  -- Nondegeneracy is preserved:
  -- `A' * C' = C * A = A * C`,
  -- and `normSq (conj B) = normSq B`.
  have h_nondeg' : A' * C' < Complex.normSq B' := by
    simpa [A', B', C', Complex.normSq, mul_comm]
      using h_nondeg

  -- Algebraic identity for finite nonzero points.
  -- After inversion, multiplying by `|c|²` recovers the
  -- original equation.
  have h_inv : ∀ c : ℂ, c ≠ 0 →
      (A' * Complex.normSq c⁻¹
        + 2 * (B'.re * (c⁻¹).re + B'.im * (c⁻¹).im)
        + C') * Complex.normSq c
      =
      A * Complex.normSq c
        + 2 * (B.re * c.re + B.im * c.im)
        + C := by
    intro c hc
    have hcn : Complex.normSq c ≠ 0 := by
      intro h0
      exact hc (Complex.normSq_eq_zero.mp h0)
    simp only [map_inv₀, Complex.conj_re, Complex.inv_re,
     Complex.conj_im, Complex.inv_im, neg_mul, A', B', C']
    field_simp [hcn]
    ring

  refine ⟨⟨A', B', C', h_nondeg'⟩, ?_⟩

  ext z
  constructor
  · -- Forward inclusion.
    rintro ⟨w, hw, rfl⟩
    cases w with
    | none =>
        -- `∞` maps to `0`.
        -- Original membership at infinity means `A = 0`.
        have hA : A = 0 := by
          simpa [Cirline.set] using hw

        -- Need to show `0` lies on the inverted circline.
        -- Its equation is `C' = A = 0`.
        simpa [Cirline.set, A', B', C', Complex.normSq] using hA

    | some c =>
        by_cases hc : c = 0
        · subst c
          -- `0` maps to `∞`.
          -- Original membership at `0` means `C = 0`,
          -- which is exactly `A' = 0`,
          -- i.e. infinity lies on the new circline.
          have hC : C = 0 := by
            simpa [Cirline.set, Complex.normSq] using hw
          -- `(some 0)⁻¹ = ∞, and membership of `none`
          change ((0 : EComplex))⁻¹ ∈ _
          rw [EComplex.zero_inv]
          exact hC

        · -- Nonzero finite point.
          have hw0 :
              A * Complex.normSq c
                + 2 * (B.re * c.re + B.im * c.im)
                + C = 0 := by
            simpa [Cirline.set] using hw

          have hcn : Complex.normSq c ≠ 0 := by
            exact fun h0 => hc (Complex.normSq_eq_zero.mp h0)

          have hmul :
              (A' * Complex.normSq c⁻¹
                + 2 * (B'.re * (c⁻¹).re + B'.im * (c⁻¹).im)
                + C') * Complex.normSq c = 0 := by
            rw [h_inv c]
            · exact hw0
            · exact hc

          have hw' :
              A' * Complex.normSq c⁻¹
                + 2 * (B'.re * (c⁻¹).re + B'.im * (c⁻¹).im)
                + C' = 0 := by
            exact (mul_eq_zero.mp hmul).resolve_right hcn

          -- The image of `some c` is `some c⁻¹`.
          change ((c : EComplex))⁻¹ ∈ _
          rw [← EComplex.coe_inv c hc]
          exact hw'

  · -- Reverse inclusion.
    intro hz
    cases z with
    | none =>
        -- To hit `∞`, use the preimage `0`.
        -- New membership at infinity says `A' = C = 0`,
        -- which means `0` lies on the old circline.
        have hC : C = 0 := by
          simpa [Cirline.set, A'] using hz

        refine ⟨EComplex.some 0, ?_, ?_⟩
        · simpa [Cirline.set, Complex.normSq] using hC
        · -- `(0)⁻¹ = ∞`.
          change ((0 : EComplex))⁻¹ = none
          exact EComplex.zero_inv

    | some c =>
        by_cases hc : c = 0
        · subst c
          -- To hit `0`, use the preimage `∞`.
          -- New membership at `0` says `C' = A = 0`,
          -- which means infinity lies on the old circline.
          have hA : A = 0 := by
            simpa [Cirline.set, A', B', C', Complex.normSq] using hz

          refine ⟨none, ?_, ?_⟩
          · simpa [Cirline.set] using hA
          · -- `∞⁻¹ = 0`.
            rfl

        · -- Nonzero finite point.
          -- Its preimage is `c⁻¹`.
          refine ⟨EComplex.some c⁻¹, ?_, ?_⟩
          · have hz0 :
                A' * Complex.normSq c
                  + 2 * (B'.re * c.re + B'.im * c.im)
                  + C' = 0 := by
              simpa [Cirline.set] using hz

            have hinv_inv : (c⁻¹)⁻¹ = c := by
              exact inv_inv c

            have hz' :
                A * Complex.normSq c⁻¹
                  + 2 * (B.re * (c⁻¹).re + B.im * (c⁻¹).im)
                  + C = 0 := by
              have h := h_inv c⁻¹
              rw [hinv_inv] at h
              rw [← h]
              · simp [hz0]
              · exact inv_ne_zero hc

            simpa [Cirline.set] using hz'

          · -- `(c⁻¹)⁻¹ = c`.
            show (EComplex.some c⁻¹)⁻¹ = Option.some c
            rw [← EComplex.coe_inv c⁻¹ (inv_ne_zero hc),
               inv_inv]


/-! ### Step 2:
  The basic generators act as the expected set maps -/

/-- The LFT `translation t` acts as `z ↦ z + t`. -/
lemma translation_apply_eq (t : ℂ) (z : EComplex) :
    (LinearFracTrans.translation t) z = z + (t : EComplex)
  := by
  cases z with
  | none => simp [LinearFracTrans.apply,
    LinearFracTrans.translation]
  | some c =>
      simp only [LinearFracTrans.apply,
        LinearFracTrans.translation, if_pos]
      norm_num
      norm_cast
      ring

/-- The LFT `scaling k` acts as `z ↦ k * z`. -/
lemma scaling_apply_eq (k : ℂ) (hk : k ≠ 0) (z : EComplex):
    (LinearFracTrans.scaling k hk) z = (k : EComplex) * z
  := by
  cases z with
  | none => simp [LinearFracTrans.apply,
      LinearFracTrans.scaling]
  | some c =>
      simp only [LinearFracTrans.apply,
        LinearFracTrans.scaling, if_pos]
      norm_num

/-- The LFT `inversion` acts as `z ↦ z⁻¹`. -/
lemma inversion_apply_eq (z : EComplex) :
    LinearFracTrans.inversion z = z⁻¹ := by
  cases z with
  | none => simp [LinearFracTrans.apply,
      LinearFracTrans.inversion]; norm_cast
  | some c =>
      by_cases hc : c = 0
      · subst hc
        simp only [LinearFracTrans.apply,
          LinearFracTrans.inversion]
        norm_num
        rw [show ((0:ℂ):EComplex) = (0:EComplex) from
          by norm_cast, zero_inv]
      · simp only [LinearFracTrans.apply,
          LinearFracTrans.inversion]
        norm_num [hc]


/-- ### Step 3:
Each basic generator preserves circlines
The name `apply` means that we apply the basic generators
to a cirline, and the image is also a cirline.
-/
lemma translation_apply_maps_cirline
  (S : Set EComplex) (t : ℂ)
    (h : isCirline S) :
    isCirline ((LinearFracTrans.translation t).apply '' S)
  := by
  have hfun : (LinearFracTrans.translation t).apply '' S
      = (fun z => z + (t : EComplex)) '' S := by
    apply Set.image_congr
    intro z _
    exact translation_apply_eq t z
  rw [hfun]
  exact translation_maps_cirline S t h

lemma scaling_apply_maps_cirline
  (S : Set EComplex) (k : ℂ) (hk : k ≠ 0)
    (h : isCirline S) :
    isCirline ((LinearFracTrans.scaling k hk).apply '' S)
  := by
  have hfun : (LinearFracTrans.scaling k hk).apply '' S
      = (fun z => (k : EComplex) * z) '' S := by
    apply Set.image_congr
    intro z _
    exact scaling_apply_eq k hk z
  rw [hfun]
  exact scaling_maps_cirline S k hk h

lemma inversion_apply_maps_cirline (S : Set EComplex)
    (h : isCirline S) :
    isCirline (LinearFracTrans.inversion.apply '' S)
  := by
  have hfun : LinearFracTrans.inversion.apply '' S
      = (fun z => z⁻¹) '' S := by
    apply Set.image_congr
    intro z _
    exact inversion_apply_eq z
  rw [hfun]
  exact inversion_maps_cirline S h


/-! ### Step 4: A decomposable LFT preserves circlines -/
/-- Any LFT that is decomposable into basic generators
  preserves circlines. -/
lemma decomposable_maps_cirline (f : LinearFracTrans)
    (hf : IsDecomposable f) :
  ∀S: Set EComplex, isCirline S → isCirline (f.apply '' S)
  := by
  induction hf with
  | translation t =>
      intro S h
      exact translation_apply_maps_cirline S t h
  | scaling k hk =>
      intro S h
      exact scaling_apply_maps_cirline S k hk h
  | inversion =>
      intro S h
      exact inversion_apply_maps_cirline S h
  | comp f g _ _ ihf ihg =>
      intro S h
      have hfun : (f.comp g).apply '' S
          = f.apply '' (g.apply '' S) := by
        rw [Set.image_image]
        apply Set.image_congr
        intro z _
        exact comp_apply f g z
      rw [hfun]
      exact ihf _ (ihg _ h)


/-! ### Step 5: Main theorem. Theorem 2.3.1 -/

/--
  Linear fractional transformations preserve circlines.
  Every linear fractional transformation maps a circle/line
  in the extended complex plane to a circle/line. The proof
  decomposes the LFT into translations, scalings and
  inversions (`isDecomposable`) and uses that each of these
  basic generators preserves circlines. -/
theorem lft_maps_cirline
  (f : LinearFracTrans) -- f is an LFT
  (S : Set EComplex)  -- S is a set in EComplex
  (h : isCirline S) -- assume S is a cirline
    : isCirline (f.apply '' S)
  -- prove that the image of S through f is a cirline
  :=  decomposable_maps_cirline f
    (LinearFracTrans.isDecomposable f) S h



end LFT_Cirline   -- end namespace

end LFT_CircleLine  -- end section

end LinearFracTrans
