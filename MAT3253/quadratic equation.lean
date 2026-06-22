import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

/-

Verify the formula for solving quadratic equation.

The first theorem consider the simplified version x^2=c.
The second theorem verify the quadratic formula for monic polynomial x^2 +bx +c

-/



open Complex

-- Solve equation x^2=c for some constant compelx number c
--
-- The two solutions are ±d, where d is a complex number satisfying
--  d^2 = c.
--
theorem solve_square_eq_constant
   {c d x : ℂ} (h : d^2 = c) (h₁: x^2 = c): x=d ∨ x=-d := by
  have h₂ : (x-d)*(x+d) = 0 := calc
  (x-d)*(x+d) = x^2 - d^2 := by ring
   _ = c - c := by rw [h, h₁]
   _ = 0 := by ring
  have h₃ : x - d = 0 ∨  x + d = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h₂
  obtain h₄ | h₅ := h₃
  · left
    calc
    x = (x-d)+d := by ring
    _ = 0 + d := by rw [h₄]
    _ = d := by ring
  · right
    calc
    x = (x+d)-d := by ring
    _ = 0 - d := by rw [h₅]
    _ = - d := by ring

-- Prove that the roots of polynomial x^2+bx+c are -b/2 ± (√disc)/2
-- where disc is the discriminant b^2-4c
--
-- Reduce the problem to the case with zero degree-1 term
-- and apply the previous theorem
--
theorem solve_quadratic (b c d x : ℂ) (h: d^2 = b^2/4-c) (h₁ : x^2+b*x+c=0):
x=-b/2+d ∨ x = -b/2-d := by
  let y:ℂ := x+b/2
  have h₂: y^2 + c - b^2/4 = 0 :=
  calc
    y^2 + c - b^2/4 = y^2 +c + b^2/4- b^2/2 := by ring
    _   = (y-b/2)^2 +b*(y- b/2) +c := by ring
    _   = x ^2 + b*x+c := by simp
    _   = 0 := h₁
  have h₃ : y^2 = b^2/4 - c :=
  calc
    y^2 = (y^2 +c - b^2/4) + b^2/4 -c := by ring
      _ = 0 + b^2/4 - c := by rw [h₂]
      _ = b^2/4 - c := by ring
  have h₄ : y = d ∨ y = -d := solve_square_eq_constant h h₃
  obtain h₅ | h₆ := h₄
  · left
    calc
      x = y-b/2 := eq_sub_of_add_eq rfl
      _ = -b/2 +y := by ring
      _ = - b/2+d:= by rw [h₅]
  · right
    calc
      x = y-b/2 := eq_sub_of_add_eq rfl
      _ = -b/2 +y := by ring
      _ = -b/2 + (-d) := by rw [h₆]
      _ = -b/2 - d := by ring
