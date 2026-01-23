/-

 Lean Solution to selected exercises in Homework 1

-/

import Mathlib.Tactic

open Complex -- open the Complex namespace to access complex numbers and operations

/-
Exercise 1a 
  (√2-i)	-i(1-√2i)= -2i 
-/
theorem question_1a : (√2 - I) 
  - I * (1 - (√2 : ℂ) * I) = -2 * I := by
  calc  
      -- (√2-i)	-i(1-√2i)
        (√2 - I) - I * (1 - √2 * I)
      -- =  √2-i-i+√2*i*i
      = √2- I - I + √2  * (I * I) := by ring
      -- = √2-i-i+√2*(-1)
    _ = √2  - I - I + √2 * (-1) := by rw [I_mul_I]
      -- = -2i
    _ = -2 * I := by
            ring

/-
  Exercise 2
  Use the associative law for addition and the distributive law to show that
     z * (z₁ + z₂ + z₃) = z * z₁ + z * z₂ + z * z₃
-/
example (z z₁ z₂ z₃ : ℂ) : z * (z₁ + z₂ + z₃) = z * z₁ + z * z₂ + z * z₃ := by
  -- 1. Distribute z over the sum (z₁ + z₂) + z₃
  rw [mul_add]       -- gives: z * (z₁ + z₂) + z * z₃
  
  -- 2. Distribute z over the inner sum z₁ + z₂
  rw [mul_add]       -- gives: (z * z₁ + z * z₂) + z * z₃
  

/-
Exercise 5 
Using the identity |z_1z_2| = |z_1| |z_2| and mathematical induction to show that 
|z^n| = |z|^n,   for n=1,2,3,\ldots.
-/

-- We prove this for all natural numbers n (0, 1, 2...),
-- which implies the case for n = 1, 2, 3...
theorem question_5 (z : ℂ) (n : ℕ) : ‖z^n‖ = ‖z‖ ^ n := by
  -- We proceed by induction on n
  induction n with
  | zero =>  
    -- Base Case: n = 0
    -- Goal: |z^0| = |z|^0
    -- Since z^0 = 1 and x^0 = 1, we show |1| = 1
    simp  -- solved by simplification

  | succ n ih =>
    -- Inductive Step: Assume true for n, prove for n + 1
    -- ih (Inductive Hypothesis): abs (z ^ n) = (abs z) ^ n
    calc
      ‖z ^ (n + 1)‖ 
        = ‖z ^ n * z‖     := by rw [pow_succ] -- Definition of power
      _ = ‖z^n‖  * ‖z‖   := by rw [norm_mul]  -- The specific identity |z1 z2| = |z1| |z2|
      _ = ‖z‖ ^ n * ‖z‖   := by rw [ih]       -- Apply Induction Hypothesis
      _ = ‖z‖ ^ (n + 1)     := by rw [pow_succ] -- Definition of power (in reverse)


/-
Question 8
Prove that if $z_1z_2=0$, then at least one of them is equal to zero.
-/
example (z1 z2 : ℂ) : z1 * z2 = 0 → z1 = 0 ∨ z2 = 0 := by
  intro h
  by_cases hz1 : z1 = 0
  · left; exact hz1
  · -- z1 ≠ 0, so it has an inverse; multiply the equation z1 * z2 = 0 by z1⁻¹
    have inv_mul : z1⁻¹ * z1 = 1 := by
      calc
        z1⁻¹ * z1 = z1 * z1⁻¹ := by simp [mul_comm]
        _ = 1 := by exact Complex.mul_inv_cancel hz1
    have : z2 = z1⁻¹ * (z1 * z2) := by
      calc
        z2 = 1 * z2 := by simp
        _  = (z1⁻¹ * z1) * z2 := by simp [inv_mul]
        _  = z1⁻¹ * (z1 * z2) := by simp [mul_assoc]
    -- now we want to show z1 = 0 ∨ z2 = 0 
    -- use h to conclude z2 = 0
    right
    calc
      z2 = z1⁻¹ * (z1 * z2) := this
      _  = z1⁻¹ * 0 := by simp [h]
      _  = 0 := by simp

