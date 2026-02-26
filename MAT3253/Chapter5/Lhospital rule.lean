/-
 L'hospital rule for 0/0 
 The proof works for complex variable and for real variable. 
 We can comment out the line `{f g : ℂ → ℂ} {z₀ f' g' : ℂ}` and replace it with `{f g : ℝ → ℝ} {z₀ f' g' : ℝ}`, and
 the same proof will work.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Conformal

noncomputable section

open Complex Filter Topology

/-- 
L'Hôpital's Rule for complex differentiable functions at a point where both vanish.
If f(z₀) = 0, g(z₀) = 0, and g'(z₀) ≠ 0, then lim (f(z)/g(z)) = f'(z₀)/g'(z₀).
-/
theorem complex_lhopital_zero_zero
--    {f g : ℝ → ℝ} {z₀ f' g' : ℝ}
    {f g : ℂ → ℂ} {z₀ f' g' : ℂ}
    (hf : HasDerivAt f f' z₀)
    (hg : HasDerivAt g g' z₀)
    (hf0 : f z₀ = 0)
    (hg0 : g z₀ = 0)
    (hg_ne : g' ≠ 0) :
    Tendsto (fun z ↦ f z / g z) (𝓝[≠] z₀) (𝓝 (f' / g')) := by

  -- By definition of the derivative, we know that 
  -- $\lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0} = f'(z_0)$ 
  -- and $\lim_{z \to z_0} \frac{g(z) - g(z_0)}{z - z_0} = g'(z_0)$.
  have h_deriv : Filter.Tendsto (fun z => (f z - f z₀) / (z - z₀)) (nhdsWithin z₀ {z₀}ᶜ) (nhds f') 
    ∧ Filter.Tendsto (fun z => (g z - g z₀) / (z - z₀)) (nhdsWithin z₀ {z₀}ᶜ) (nhds g') := by
    -- By definition of HasDerivAt, we know that the limit of (f(z) - f(z₀)) / (z - z₀) as z approaches z₀ is f', and similarly for g.
    have h_deriv_f : Filter.Tendsto (fun z => (f z - f z₀) / (z - z₀)) 
      (nhdsWithin z₀ {z₀}ᶜ) (nhds f') := by
      rw [ hasDerivAt_iff_tendsto_slope ] at hf
      simpa [ div_eq_inv_mul ] using hf
    have h_deriv_g : Filter.Tendsto (fun z => (g z - g z₀) / (z - z₀))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds g') := by
      rw [ hasDerivAt_iff_tendsto_slope ] at hg
      simpa [ div_eq_inv_mul ] using hg
    exact ⟨h_deriv_f, h_deriv_g⟩
  -- Since the denominator is non-zero, we can apply the fact that 
  -- the limit of a quotient is the quotient of the limits.
  have h_quot : Filter.Tendsto (fun z => ((f z - f z₀) / (z - z₀)) / ((g z - g z₀) / (z - z₀))) 
    (nhdsWithin z₀ {z₀}ᶜ) (nhds (f' / g')) := by
    exact h_deriv.1.div h_deriv.2 hg_ne

  -- Apply the congruence rule. 
  -- This allows us to prove the limits are the same if the functions are equal near z₀.
  apply h_quot.congr'

  -- Filter to the set of points where z ≠ z₀.
  -- The filter 𝓝[≠] z₀ guarantees we only care about z where z ≠ z₀.
  filter_upwards [self_mem_nhdsWithin] with z hz

  -- Substitute f(z₀) = 0 and g(z₀) = 0 and simplify "something - 0"
  simp only [hf0, hg0, sub_zero]

  -- Perform the algebraic cancellation of (z - z₀).
  -- We need to establish that the denominator (z - z₀) is not zero.
  have h_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  
  -- Use field_simp to cancel the common factor.
  -- Alternatively, you could use: rw [div_div_div_cancel_right _ _ h_ne]
  field_simp [h_ne]        
