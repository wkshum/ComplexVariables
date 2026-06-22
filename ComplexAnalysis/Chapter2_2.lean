import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

noncomputable section ExtendedComplex

open Complex

/-
  # Extended complex numbers
-/

/--
 We implement extended complex number by the class
 of `Option`, and use the term `none` in `Option` as
 the point at infinity.
-/
def EComplex := Option ℂ


namespace EComplex

-- Notation for extended complex numbers
notation "ℂ∞" => EComplex

-- Decidable equality for EComplex
instance decidableEq : DecidableRel ((· = ·)
  : EComplex → EComplex → Prop) :=
  Option.instDecidableEq

/-- Embedding ℂ in EComplex by the canonical inclusion
-/
@[coe, match_pattern] abbrev some : ℂ  → EComplex :=
  Option.some


/-
##  The point at infinity
-/

-- Define the notation of infty for the point at infinity
notation "∞" => (none : EComplex)

/-- Alias for the point at infinity
-/
abbrev infty : EComplex := none

/-- infinity is identified with none in Option
-/
theorem infty_eq_none : infty = none := by rfl

/- Making EComplex an instance of Nontrivial
-/
deriving instance Nontrivial
  for EComplex



-- testing notation
-- Check that infinity is not equal to 1
#eval ∞ ≠ some 1  -- True

-- Create instances for 0 and 1
instance : Zero EComplex := ⟨some 0⟩
instance : One EComplex := ⟨some 1⟩



/-
## Displaying a term in EComplex
-/

-- printing a complex number
unsafe instance : ToString ℂ where
  toString z := s!"{repr z.re} + {repr z.im}i"

-- printing an extended complex number
unsafe def printEComplex (x : EComplex) : String :=
  match x with
  | none => "∞"
  | Option.some val => s!"{val}"

-- example of printing an extended complex number
#eval printEComplex (some (1 + 2*I))

-- Testing the print function
#eval printEComplex (none) -- should print "∞"
#eval printEComplex ∞     -- Output: "∞"
#eval printEComplex infty -- Output: "∞"




/-
  ## Coercion from Complex to EComplex
-/



-- Coersion from type ℂ to type EComplex
@[coe, match_pattern] def Complex.toEComplex :
  ℂ  → EComplex := EComplex.some

instance coe : Coe ℂ  EComplex :=
  ⟨EComplex.some⟩

-- Auxiliary class implementing `Coe*`.
instance : CoeTC ℂ EComplex := ⟨EComplex.some⟩

-- EComplex is inhabited, it has at least one element
instance : Inhabited EComplex := ⟨ (0:ℂ) ⟩

-- Enable writing any natural number (2, 3, 4...)
-- as complex number
instance (n : ℕ) [OfNat ℂ n] : OfNat EComplex n
  := ⟨some (OfNat.ofNat n)⟩

-- Testing the coercion
#check some (8 : ℂ)   -- ↑8 : ℂ∞


-- Coercion of 0 and 1 into EComplex type

@[simp]
theorem coe_zero : ((0 : ℂ) : EComplex) = (0:ℂ) := rfl

@[simp]
theorem coe_one : ((1 : ℂ) : EComplex) = (1:ℂ) := rfl



-- Give a name `zero` to the zero in EComplex
def zero : EComplex := some ⟨0 , 0⟩

-- Define the function toComplex : EComplex → ℂ
-- the point at infinity is mapped to 0 in ℂ
def toComplex : EComplex → ℂ
  | ∞ => 0
  | (x : ℂ ) => x

/--
 Some theorems to help coercion for the simp tactic
-/
@[simp]
theorem toComplex_Inf : toComplex ∞ = 0 :=
  rfl

@[simp]
theorem some_eq_coe (z : ℂ) :
    some z = (z : EComplex) := rfl

@[simp]
theorem coe_eq_some (z : ℂ) :
    (z : EComplex) = some z := rfl

@[simp]
theorem option_some_eq_coe (z : ℂ) :
    Option.some z = (z : EComplex) := rfl


/-- Theorem: toComplex x = 0  iff x = ∞  or x = some 0 -/
@[simp]
theorem toComplex_eq_zero_iff (x : EComplex)
    : toComplex x = 0 ↔ x = none ∨ x = some 0 := by
  constructor
  · unfold toComplex
    rcases x with ⟨z⟩ | _
    · simp
    · simp ; intro h ; exact congrArg Option.some h
  · intro h
    rcases h with h1 | h2
    · rw [h1] ; rfl
    · rw [h2] ; rfl

/-- toEComplex is injective on the subset of EComplex
that excludes ∞
-/
@[simp]
lemma some_eq_iff (a b : ℂ)
  : (Complex.toEComplex a = Complex.toEComplex b)
    ↔ (a = b) := by
  rw [iff_eq_eq]
  exact Option.some.injEq a b

/-- the coercion toEComplex is injective -/
theorem coe_injective :
  Function.Injective Complex.toEComplex := by
  unfold Function.Injective
  intro a b hab
  exact (some_eq_iff a b).mp hab

/-- the coercion toEComplex is injective,
restated in terms of the coercion notation for norm_cast
-/
@[norm_cast]
theorem coe_eq_coe {x y : ℂ} :
  (x : EComplex) = y ↔ x = y :=
  coe_injective.eq_iff

/-- the coercion toEComplex is injective,
 restated in terms of the coercion notation for norm_cast
-/
@[simp, norm_cast]
theorem coe_eq_coe_iff {x y : ℂ} :
  (x : EComplex) = (y : EComplex) ↔ x = y :=
  coe_injective.eq_iff

/-- the coercion toEComplex is injective,
restated in terms of inequality
-/
theorem coe_ne_coe_iff {x y : ℂ} :
  (x : EComplex) ≠ (y : EComplex) ↔ x ≠ y :=
  coe_injective.ne_iff


-- if some a ≠ some b ,then a ≠ b
@[simp]
theorem some_neq_imply_tocomplex_neq {a b : ℂ} :
  some a ≠ some b ↔ a ≠ b := by
  exact EComplex.coe_ne_coe_iff

/-
  ## Complex addition and complex multiplication
-/


section ComplexAdditionMultiplication
/-
  Arithmetic operations on EComplex are defined by
  extending the corresponding operations on ℂ
-/

/--
  Addition of extended complex numbers
-/
@[simp]
protected def add : EComplex → EComplex → EComplex
  | ∞, ∞ => ∞
  | (z : ℂ), ∞ => ∞
  | ∞, (z : ℂ) => ∞
  | (z : ℂ), (w : ℂ) => (z + w : ℂ)

/--
  Multiplication of extended complex numbers
-/
@[simp]
protected def mul : EComplex → EComplex → EComplex
  | ∞, ∞ => ∞
  | (z : ℂ), ∞ => ∞
  | ∞, (z : ℂ) => ∞
  | (z : ℂ), (w : ℂ) => (z * w : ℂ)

-- defining addition and multiplication instances
-- for the EComplex type
instance : Add EComplex := ⟨EComplex.add⟩
instance : Mul EComplex := ⟨EComplex.mul⟩

-- addition in EComplex type
theorem EComplex_addition (x : EComplex) (y : EComplex)
  : EComplex.add x y = x + y := by simp; rfl

-- multiplication in EComplex type
theorem EComplex_multiplication
  (x : EComplex) (y : EComplex)
  : EComplex.mul x y = x * y := by simp; rfl

/-- z + ∞ = ∞ -/
@[simp]
theorem finite_add_infinity {z : ℂ} :
  z + infty = infty := by rfl

/-- ∞ + z = ∞ -/
@[simp]
theorem infinity_add_finite {z : ℂ} :
  infty + z = infty := by rfl

/-- z · ∞ = ∞ -/
@[simp]
theorem finite_mul_infinity {z : ℂ} :
  z * infty = infty := by rfl

/-- ∞ · z = ∞ -/
@[simp]
theorem infinity_mul_finite {z : ℂ} :
  infty * z = infty := by rfl

/-- In measure theory, we usally define 0·∞ =  0
But in this implementation we define 0·∞ = ∞
-/
example : infty * (0:ℂ) = infty := by rfl


-- testing addition and multiplication
example : (some 3) + (some 4) = some 7
  := by rw [ ←EComplex_addition] ; simp; ring
example : infty + (some 3) = infty := by rfl
example : infty + (some 4 : EComplex) = infty := by rfl
example : infty + infty = infty := by rfl
example : infty * infty = infty := by rfl
example : infty * (some 4 : EComplex) = infty := by rfl

end ComplexAdditionMultiplication


/-
 ## Complex subtrraction
-/

section ComplexSubtraction

/--
  Subtraction of extended complex numbers
  is defined by extending the corresponding operation on ℂ
-/
@[simp]
protected def sub : EComplex → EComplex → EComplex :=
  fun z w => z + (-1:ℂ)*w

-- In this implementation, ∞ - ∞ is defined as ∞
example : EComplex.sub infty infty = infty := by exact rfl

instance : Sub EComplex := ⟨EComplex.sub⟩

instance : Neg EComplex := ⟨fun z ↦ (-1:ℂ)*z⟩


@[simp]
theorem EComplex_subtraction {x y : EComplex}
  : EComplex.sub x y = x - y := by rfl

@[norm_cast]
theorem coe_mul {x y : ℂ} :
  (↑(x * y) : EComplex) = x * y :=
  rfl

@[norm_cast]
theorem coe_add {x y : ℂ} : (↑(x + y)
  : EComplex) = x + y :=
  rfl

@[simp, norm_cast]
theorem coe_neg {z : ℂ} : (↑(-z) : EComplex) = -↑z := by
  congr ; ring

@[norm_cast]
theorem coe_mul_some {x y : ℂ} : (↑x * (some y)
  : EComplex) = ↑ (x * y) :=
  rfl

@[norm_cast]
theorem some_mul_coe {x y : ℂ} : ((some x) * ↑y
  : EComplex) = ↑(x * y) :=
  rfl

@[norm_cast]
theorem coe_add_some {x y : ℂ} :
  (↑x + (some y) : EComplex) = ↑(x + y) :=
  rfl

@[norm_cast]
theorem some_add_coe {x y : ℂ}
  : ((some x) + ↑y : EComplex) = ↑(x + y) :=
  rfl

/-- if x and y are both finite complex number and x ≠ y,
  then x-y is also a finite complex number and x-y ≠ 0
-/
theorem finite_EComplex_sub_ne_zero {x y : EComplex}
  (hxy : x ≠ y) (hx : x ≠ ∞) (hy : y ≠ ∞)
  : (x - y).toComplex ≠ 0 := by
  cases x
  cases y <;>
  · contradiction
  cases y
  · contradiction
  · rw [← EComplex_subtraction]
    unfold EComplex.sub
    rw [← EComplex_multiplication]
    rw [← EComplex_addition]
    unfold EComplex.add
    unfold EComplex.mul
    simp only [neg_mul, one_mul, ne_eq,
    toComplex_eq_zero_iff, EComplex.coe_eq_coe_iff, not_or]
    constructor
    · push Not
      exact not_eq_of_beq_eq_false rfl
    · push Not
      intro h
      apply hxy
      rw [← sub_eq_add_neg, sub_eq_zero] at h
      rw [h]

-- Some type checking
#check some 3 - some 5   -- ↑3 - ↑5 : ℂ∞
#check some 3 * some 5   -- ↑3 * ↑5 : ℂ∞

-- prove that 3 - 5 = -2 in EComplex type
example : some 3 - some 5 = some (-2) := by
  -- Convert subtraction to your definition
  rw [← EComplex_subtraction]
  -- Unfold the logic to see the underlying
  -- complex operations
  simp [EComplex.sub]
  norm_cast

end ComplexSubtraction


/-
  ## Complex division and the inversion function
-/

section ComplexDivision

/--
  Complex inversion
-/
@[simp]
protected def inv : EComplex → EComplex
  | ∞ => (0:ℂ)
  | (z : ℂ) => if z=(0:ℂ) then ∞ else (z⁻¹ : ℂ)

instance : Inv (EComplex) := ⟨EComplex.inv⟩

/--
  Complex division

  Define z/w by z * inv (w)
-/
protected def div : EComplex → EComplex → EComplex :=
  fun z w => z * (EComplex.inv w)

instance : Div (EComplex) := ⟨EComplex.div⟩

/--
  Theorems on coercion for complex division
-/
@[simp, norm_cast]
theorem coe_inv (z : ℂ) (hz : z ≠ 0) :
  (↑(z⁻¹) : EComplex) = (↑z)⁻¹ := by
  -- Unfold the EComplex definition of inverse
  simp only [Inv.inv, EComplex.inv]
  -- Simplify the 'if' condition using the fact that z ≠ 0
  rw [if_neg hz]


@[simp, norm_cast]
theorem coe_div (x y : ℂ) (hy : y ≠ 0) :
  (↑(x / y) : EComplex) = x / y := by
  -- Rewrite division as multiplication by inverse
  rw [div_eq_mul_inv]
  rw [coe_mul]
  -- Use our multiplication and inverse coercions
  rw [coe_inv y hy]
  -- Everything matches
  rfl


/-- 1 / ∞ = 0  -/
@[simp]
theorem infty_inv : Inv.inv infty = 0 := by
  rfl

/-- 1 / 0 = ∞  -/
@[simp]
theorem zero_inv : Inv.inv (0: EComplex) = infty := by
  simp only [Inv.inv, EComplex.inv]
  rfl

/-- z/∞ = 0  for all z:ℂ  -/
@[simp]
theorem complex_div_infty {z : ℂ} :
  (z : EComplex).div infty = 0 := by
  simp [EComplex.div, infty, EComplex.inv]
  -- now goal is (↑z * ↑0) = 0, unfold mul and reduce
  norm_cast
  congr
  ring

/-- z/∞ = 0  for all z:ℂ  -/
@[simp]
theorem complex_div_infty_slash {z : ℂ} :
  (z : EComplex) / infty = 0 := by
  -- `/` is the same as `.div`; make that explicit
  change (z : EComplex).div infty = 0
  simp [complex_div_infty (z := z)]

/-- Usually, ∞/∞ is undefined,
  but in this implementation, we have ∞/∞ = ∞
  by convention
-/
example : infty.div infty = infty := by
  simp [EComplex.div, infty, EComplex.inv]

/--  0 / 1 = 0 -/
example : some 0 / some 1 = some 0 := by
  change EComplex.div ↑0 ↑1 = some 0
  unfold EComplex.div
  unfold EComplex.inv
  simp only [one_ne_zero, ↓reduceIte, inv_one]
  change EComplex.mul ↑0 ↑1 = some 0
  unfold EComplex.mul
  simp

end ComplexDivision



/-
  ## EComplex arithmetic lemmas
-/

section ComplexArithmeticLemmas


@[simp]
lemma sub_some {a b : ℂ} :
    some a - some b = some (a - b) := by
  rw [← EComplex_subtraction]
  unfold EComplex.sub
  rw [← EComplex_multiplication]
  unfold EComplex.mul
  simp only [neg_mul, one_mul, coe_neg]
  rw [← coe_neg]
  exact ((fun a ↦ a) ∘ fun a ↦ a) rfl

@[simp]
lemma div_some {a b : ℂ} (hb : b ≠ 0) :
    some a / some b = some (a / b) := by
  rw [← coe_div]
  exact hb

@[simp]
lemma mul_some {a b : ℂ} :
    some a * some b = some (a * b) := by
  exact coe_mul_some

/-- Negation cancellation for division
-/
@[simp]
lemma neg_div_neg {a b : ℂ} (hb : b ≠ 0) :
    some (-a) / some (-b) = some a / some b := by
  rw [@div_some (-a) (-b) (neg_ne_zero.mpr hb)]
  rw [@div_some a b hb]
  congr 1
  field_simp


/-- Difference is antisymmetric
-/
@[simp]
lemma sub_antisymm {a b : ℂ} :
    some a - some b = -(some b - some a) := by
  rw [@sub_some a b, @sub_some b a]
  congr 1
  ring

/-- Negation of (some z) is some (-z)
-/
@[simp]
lemma neg_some {a : ℂ} :
    -(some a : EComplex) = some (-a) := by
  exact Eq.symm coe_neg

/-- assuming both a and b are nonzero complex numbers
   Division reciprocal: 1 / (a / b) = b / a
-/
@[simp]
lemma one_div_div {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (1 : EComplex) / (some a / some b) = some b / some a
  := by
  rw [div_some hb, div_some ha]
  rw [coe_div,coe_div]
  change EComplex.div ↑1 (some a / some b)
    = EComplex.div (some b)  (some a)
  unfold EComplex.div
  change 1 * (EComplex.div (some a) (some b)).inv
    = some b * (some a).inv
  unfold EComplex.div EComplex.inv
  simp only [hb,ha,↓reduceIte]
  rw [← EComplex_multiplication,←EComplex_multiplication,
    ← EComplex_multiplication]
  unfold EComplex.mul
  simp only [mul_eq_zero, inv_eq_zero, mul_inv_rev,
    inv_inv,ha,hb]
  simp only [or_self, ↓reduceIte, one_mul]
  exact ha
  exact hb

/-- Addition of EComplex is commutative
-/
@[simp]
lemma add_comm_ecomplex {x y : EComplex} :
    x + y = y + x := by
  change EComplex.add x y = EComplex.add y x
  unfold EComplex.add
  cases x <;> cases y <;> simp only [add_comm]


/-- Multiplication of EComplex is commutative
-/
@[simp]
lemma mul_comm_ecomplex {x y : EComplex} :
    x * y = y * x := by
  change EComplex.mul x y = EComplex.mul y x
  unfold EComplex.mul
  cases x <;> cases y <;> simp only [mul_comm]


/-- Product of fractions
  (a/b)*(c/d) = (ac)/(bd)
-/
@[simp]
lemma div_mul_div {a b c d : ℂ}
  (hb : b ≠ 0) (hd : d ≠ 0) :
  (some a / some b) * (some c / some d)
    = some (a * c) / some (b * d) := by
  rw [div_some hb, div_some hd]
  rw [@mul_some (a / b) (c / d)]
  rw [@div_some (a * c) (b * d) (mul_ne_zero hb hd)]
  congr 1
  field_simp

/-- Division by itself equals 1
  a/a = 1  if a≠0
-/
@[simp]
lemma div_self_some {a : ℂ} (ha : a ≠ 0) :
    some a / some a = (1 : EComplex) := by
  rw [div_some ha]
  congr 1
  field_simp

/--
  Assume b is nonzero.
  Then b*(a/b) = a
-/
@[simp]
lemma mul_div_self {a b : ℂ} (hb : b ≠ 0) :
    (some b) * (some a / some b) = some a := by
  rw [div_some hb, @mul_some b (a / b)]
  congr 1
  field_simp

/--
  Assume a and b are nonzero
  Then (a/b) * (c/a) = c/b
-/
@[simp]
lemma div_mul_div_cancel (a b c : ℂ)
  (ha : a ≠ 0) (hb : b ≠ 0) :
  (some a / some b) * (some c / some a) = some c / some b := by
  rw [div_some, div_some, div_some, ← coe_mul]
  congr 1
  field_simp
  exact hb
  exact ha
  exact hb

/--
  Assume y is not zero.
  Then 1 - (x/y) = (y-x)/x in EComplex
-/
@[simp]
lemma one_sub_div {x y : ℂ} (hy : y ≠ 0) :
    (1 : EComplex) - some x / some y = some (y - x) / some y := by
  rw [div_some hy, @div_some (y - x) y hy]
  rw [← EComplex_subtraction]
  unfold EComplex.sub
  rw [← EComplex_addition]
  unfold EComplex.add
  have hprod : (↑(-1 : ℂ) : EComplex) * (↑(x / y) : EComplex) = some ((-1) * (x / y)) := rfl
  have h1 : (1 : EComplex) = some (1 : ℂ) := rfl
  rw [h1, hprod]
  simp only [neg_mul, one_mul, coe_eq_coe_iff]
  field_simp
  ring

/--
  Asume b and d are nont zero.
  1 - (a/b) * (c/d) = (b * d -a * c) / bc
-/
@[simp]
lemma one_sub_mul_div_div (a b c d : ℂ) (hb : b ≠ 0) (hd : d ≠ 0) :
     (1 : EComplex) - (some a / some b) * (some c / some d) =
     some (b * d - a * c) / some (b * d) := by
  rw [@div_mul_div a b c d hb hd]
  rw [@one_sub_div (a * c) (b * d) (mul_ne_zero hb hd)]

end ComplexArithmeticLemmas


end EComplex

end ExtendedComplex
