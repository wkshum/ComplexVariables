/-
  Solution to question 4 in homework 3

  Question: Show that
\[
\lim_{z \to z_0} f(z)g(z) = 0 \quad \text{if} \quad \lim_{z \to z_0} f(z) = 0
\]
and if there exists a positive number \( M \) such that \( |g(z)| \leq M \) 
for all \( z \) in some neighborhood of \( z_0 \).
-/ 

/- 
Standard Epsilon-Delta definition of a limit for complex functions.
lim_{z → z₀} f(z) = L
-/
def IsLimit (f : ℂ → ℂ) (z₀ L : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z, dist z z₀ < δ → dist (f z) L < ε

/- 
Standard definition of "Locally Bounded".
There exists M > 0 and a neighborhood (radius δ) where |g(z)| ≤ M.
-/
def IsLocallyBounded (g : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ M > 0, ∃ δ > 0, ∀ z, dist z z₀ < δ → ‖g z‖ ≤ M

/-
The Theorem: If f(z) → 0 and g(z) is locally bounded, then f(z)g(z) → 0.
-/
theorem limit_mul_eq_zero_epsilon_delta (f g : ℂ → ℂ) (z₀ : ℂ)
    (h_lim : IsLimit f z₀ 0)
    (h_bdd : IsLocallyBounded g z₀) :
    IsLimit (fun z ↦ f z * g z) z₀ 0 := by
  -- 1. Let ε > 0 be given.
  intro ε hε
  
  -- 2. Extract M and δ_g from the boundedness hypothesis.
  rcases h_bdd with ⟨M, hM_pos, δ_g, hδg_pos, hg_bound⟩
  
  -- 3. We want to make |f(z)| < ε / M.
  --    Let's verify ε / M is positive.
  let ε_target := ε / M
  have h_target_pos : ε_target > 0 := div_pos hε hM_pos

  -- 4. Use the limit hypothesis of f to find δ_f for this ε_target.
  rcases h_lim ε_target h_target_pos with ⟨δ_f, hδf_pos, hf_bound⟩

  -- 5. Choose δ = min(δ_f, δ_g).
  use min δ_f δ_g
  
  -- We must prove two things: δ > 0, and the inequality holds.
  constructor
  · -- Prove δ > 0
    exact lt_min hδf_pos hδg_pos
  
  · -- Prove the inequality: |f(z)g(z) - 0| < ε
    intro z hz
    rw [dist_zero_right, norm_mul] -- Rewrite |f(z)g(z) - 0| as |f(z)| * |g(z)|

    -- We know dist z z₀ < min δ_f δ_g, implies it is smaller than both.
    have hz_f : dist z z₀ < δ_f := lt_of_lt_of_le hz (min_le_left _ _)
    have hz_g : dist z z₀ < δ_g := lt_of_lt_of_le hz (min_le_right _ _)

    -- Get the specific bounds for this z
    have h_norm_f : ‖f z‖ < ε / M := by
      -- dist (f z) 0 is just ‖f z‖
      rw [← dist_zero_right]
      exact hf_bound z hz_f
    
    have h_norm_g : ‖g z‖ ≤ M := hg_bound z hz_g

    -- 6. Final Calculation
    calc ‖f z‖ * ‖g z‖
      _ ≤ ‖f z‖ * M   := mul_le_mul_of_nonneg_left h_norm_g (norm_nonneg (f z))
      _ < (ε / M) * M := mul_lt_mul_of_pos_right h_norm_f hM_pos
      _ = ε           := div_mul_cancel₀ ε (ne_of_gt hM_pos)  
