import Mathlib

/-
Formalized by Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
Theorem 11.5.1.

		Suppose $f(z,w)$ is a continuous complex function defined on $D\times \Omega \in \mathbb{C}^2$, where $D$ is an open and connected domain.
		Suppose that for each $w \in \Omega$, the function $f(z,w)$ is holomorphic in $z$.
		For any curve $C$ of finite length in $\Omega$, the function
		$$
		F(z) \triangleq \int_C f(z,w) \, dw
		$$ 	
		is holomorphic over $D$, and the derivative is given by
		$$
		F'(z) = \int_C \frac{\partial }{\partial z} f(z,w)\, dw.
		$$

-/

/-!
# Holomorphicity of Contour Integrals (Leibniz Integral Rule)
This file proves that if `f(z, w)` is holomorphic in `z` for each `w`, then the contour integral
`F(z) = ∫_C f(z, w) dw` is holomorphic, with derivative given by differentiating under the
integral sign: `F'(z) = ∫_C (∂f/∂z)(z, w) dw`.
This is a fundamental result in complex analysis, often used to establish holomorphicity of
functions defined by integral representations.

## Main results
* `contourIntegral_hasDerivAt`: The derivative of the parametric integral
  `F(z) = ∫ f(z, γ(t)) * γ'(t) dμ(t)` is given by `∫ f'_z(z₀, γ(t)) * γ'(t) dμ(t)`.
* `contourIntegral_differentiableAt`: The parametric integral is complex differentiable.
* `contourIntegral_hasDerivAt_intervalIntegral`: Version using interval integrals
  `F(z) = ∫ t in a..b, f(z, γ(t)) * γ'(t)`.
* `contourIntegral_differentiableAt_intervalIntegral`: Differentiability version for
  interval integrals.
-/


open MeasureTheory Set Filter Complex Topology
noncomputable section

/-! ### Bochner integral version -/
/-
**Leibniz integral rule for complex contour integrals (Bochner integral version).**
Suppose `f(z, w)` is a function of two complex variables, `γ : ℝ → ℂ` parametrizes a curve,
and `f'(z, w)` is the partial derivative of `f` with respect to `z`. If:
- `f(z, γ(·)) * γ'(·)` is a.e. strongly measurable for `z` near `z₀`,
- `f(z₀, γ(·)) * γ'(·)` is integrable,
- the derivative integrand is bounded by an integrable function,
- `f(·, γ(t))` has complex derivative `f'(·, γ(t))` for each `t` and `z` near `z₀`,
then `F(z) = ∫ f(z, γ(t)) * γ'(t) dμ(t)` has complex derivative
`F'(z₀) = ∫ f'(z₀, γ(t)) * γ'(t) dμ(t)`.
-/
theorem contourIntegral_hasDerivAt
    {f : ℂ → ℂ → ℂ} {f' : ℂ → ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {S : Set ℂ}
    {μ : Measure ℝ}
    (hS : S ∈ 𝓝 z₀)
    (hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t => f z (γ t) * deriv γ t) μ)
    (hF_int : Integrable (fun t => f z₀ (γ t) * deriv γ t) μ)
    (hF'_meas : AEStronglyMeasurable (fun t => f' z₀ (γ t) * deriv γ t) μ)
    {bound : ℝ → ℝ}
    (h_bound : ∀ᵐ t ∂μ, ∀ z ∈ S, ‖f' z (γ t) * deriv γ t‖ ≤ bound t)
    (h_bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ t ∂μ,
      ∀ z ∈ S, HasDerivAt (fun z => f z (γ t)) (f' z (γ t)) z) :
    HasDerivAt (fun z => ∫ t, f z (γ t) * deriv γ t ∂μ)
      (∫ t, f' z₀ (γ t) * deriv γ t ∂μ) z₀ := by
  -- Apply the `hasDerivAt_integral_of_dominated_loc_of_deriv_le` lemma with the given hypotheses.
  have h_apply : MeasureTheory.Integrable (fun t => f' z₀ (γ t) * deriv γ t) μ ∧ HasDerivAt (fun z => ∫ t, f z (γ t) * deriv γ t ∂μ) (∫ t, f' z₀ (γ t) * deriv γ t ∂μ) z₀ := by
    convert hasDerivAt_integral_of_dominated_loc_of_deriv_le _ _ _ _ _ _ _;
    any_goals tauto;
    filter_upwards [ h_diff ] with t ht using fun z hz => by simpa using HasDerivAt.mul_const ( ht z hz ) ( deriv γ t ) ;
  exact h_apply.2


/-- The contour integral of a holomorphic family is complex differentiable. -/
theorem contourIntegral_differentiableAt
    {f : ℂ → ℂ → ℂ} {f' : ℂ → ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {S : Set ℂ}
    {μ : Measure ℝ}
    (hS : S ∈ 𝓝 z₀)
    (hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t => f z (γ t) * deriv γ t) μ)
    (hF_int : Integrable (fun t => f z₀ (γ t) * deriv γ t) μ)
    (hF'_meas : AEStronglyMeasurable (fun t => f' z₀ (γ t) * deriv γ t) μ)
    {bound : ℝ → ℝ}
    (h_bound : ∀ᵐ t ∂μ, ∀ z ∈ S, ‖f' z (γ t) * deriv γ t‖ ≤ bound t)
    (h_bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ t ∂μ,
      ∀ z ∈ S, HasDerivAt (fun z => f z (γ t)) (f' z (γ t)) z) :
    DifferentiableAt ℂ (fun z => ∫ t, f z (γ t) * deriv γ t ∂μ) z₀ :=
  (contourIntegral_hasDerivAt hS hF_meas hF_int hF'_meas h_bound h_bound_int h_diff).differentiableAt


/-! ### Interval integral version -/
/-
**Leibniz integral rule for complex contour integrals (interval integral version).**
Given a curve `γ : [a, b] → ℂ` and a function `f(z, w)` with partial derivative `f'(z, w)`
in `z`, the contour integral `F(z) = ∫ t in a..b, f(z, γ(t)) * γ'(t) dt` has complex derivative
`F'(z₀) = ∫ t in a..b, f'(z₀, γ(t)) * γ'(t) dt`, provided the standard dominated convergence
conditions hold.
-/
theorem contourIntegral_hasDerivAt_intervalIntegral
    {f : ℂ → ℂ → ℂ} {f' : ℂ → ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {S : Set ℂ}
    (hS : S ∈ 𝓝 z₀)
    (hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t => f z (γ t) * deriv γ t)
        (volume.restrict (Set.uIoc a b)))
    (hF_int : IntervalIntegrable (fun t => f z₀ (γ t) * deriv γ t) volume a b)
    (hF'_meas : AEStronglyMeasurable (fun t => f' z₀ (γ t) * deriv γ t)
        (volume.restrict (Set.uIoc a b)))
    {bound : ℝ → ℝ}
    (h_bound : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      ∀ z ∈ S, ‖f' z (γ t) * deriv γ t‖ ≤ bound t)
    (h_bound_int : IntervalIntegrable bound volume a b)
    (h_diff : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      ∀ z ∈ S, HasDerivAt (fun z => f z (γ t)) (f' z (γ t)) z) :
    HasDerivAt (fun z => ∫ t in a..b, f z (γ t) * deriv γ t)
      (∫ t in a..b, f' z₀ (γ t) * deriv γ t) z₀ := by
  by_cases hab : a ≤ b;
  · simp_all +decide;
    convert contourIntegral_hasDerivAt hS hF_meas _ _ _ _ using 1;
    any_goals assumption;
    · simp_all +decide [ Filter.eventually_inf_principal, intervalIntegral.integral_of_le hab ];
    · simpa only [ intervalIntegrable_iff_integrableOn_Ioc_of_le hab ] using hF_int;
    · simp_all +decide [ Filter.eventually_inf_principal ];
    · exact h_bound_int.1;
  · simp_all +decide [ intervalIntegral, le_of_not_ge hab ];
    convert HasDerivAt.neg ( contourIntegral_hasDerivAt hS hF_meas _ hF'_meas _ _ _ ) using 1;
    all_goals rw [ intervalIntegrable_iff ] at *; simp_all +decide [ le_of_lt hab ];
    all_goals assumption

    
/-- The contour integral of a holomorphic family is complex differentiable
(interval integral version). -/
theorem contourIntegral_differentiableAt_intervalIntegral
    {f : ℂ → ℂ → ℂ} {f' : ℂ → ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {S : Set ℂ}
    (hS : S ∈ 𝓝 z₀)
    (hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t => f z (γ t) * deriv γ t)
        (volume.restrict (Set.uIoc a b)))
    (hF_int : IntervalIntegrable (fun t => f z₀ (γ t) * deriv γ t) volume a b)
    (hF'_meas : AEStronglyMeasurable (fun t => f' z₀ (γ t) * deriv γ t)
        (volume.restrict (Set.uIoc a b)))
    {bound : ℝ → ℝ}
    (h_bound : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      ∀ z ∈ S, ‖f' z (γ t) * deriv γ t‖ ≤ bound t)
    (h_bound_int : IntervalIntegrable bound volume a b)
    (h_diff : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      ∀ z ∈ S, HasDerivAt (fun z => f z (γ t)) (f' z (γ t)) z) :
    DifferentiableAt ℂ (fun z => ∫ t in a..b, f z (γ t) * deriv γ t) z₀ :=
  (contourIntegral_hasDerivAt_intervalIntegral hS hF_meas hF_int hF'_meas h_bound h_bound_int h_diff).differentiableAt
end
