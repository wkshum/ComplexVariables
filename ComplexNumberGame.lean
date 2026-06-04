import Mathlib.Tactic
import Mathlib.Data.Real.Basic


/- 
  Similar to the Natural Number Game,
  we rewrite the complex number game 
  with rationl numbers as the real and imaginary parts.

  Mathematically, the structure implemented is ℚ[i]. The real
  part and the imaginary parts are rational numbers. So that
  the examples can be print out more conveniently. Indeed,
  all calculations by hand in practice  is carried out in ℚ[i]
  instead of ℂ.
-/

-- set_option linter.dupNamespace false

namespace complex_number_game

-------------------------------------
--   Construction of complex number
-------------------------------------

-- A complex number with rational real and imaginary parts
@[ext] structure complexQ where
  re : ℚ   -- real part
  im : ℚ   -- imaginary part
 deriving Repr

notation "ℚ[i]" => complexQ

-- Display a complex number as x+y*I
unsafe instance instRepr : Repr complexQ where
  reprPrec z _  :=
    reprPrec z.re 20 ++ " + " ++ reprPrec z.im 20 ++ "*I"


-- examples of constructors

-- complex number -2+4i
def sample1 := complexQ.mk (-2) (2/3)

#eval sample1 --   -2+2I/3

-- complex number -3i
def sample2 : complexQ where
  re := 0
  im := (-3)

def sample3 : complexQ := ⟨0, -3⟩    -- complex number 0-3i

def sample4 : ℚ[i] :=   -- complex 1.5 + (3/2)i
{
 re := 1.5
 im := 3/2
}

#eval sample1   -- -2 + (2 : Rat)/3*I
#eval sample2   -- 0 + -3*I
#eval sample3   -- 0 + -3*I
#eval sample4   -- (3 : Rat)/2 + (3 : Rat)/2*I


-- Two complex numbers are equal if and only if the real and
-- imaginary parts are the same
example : sample2 = sample3 := by rfl

-- #eval sample2 = sample3   -- no meaning at this point

def sample5 : ℚ := (complexQ.mk 2 4).re  -- this term is a rational number 2

#eval sample5   -- 2

-- The real part of 2+4i is equal to 2
example :  (complexQ.mk 2 4).re = 2 := rfl

-- The imaginary part of 2+4i is equal to 4
example :  (complexQ.mk 2 4).im = 4 := rfl


-- Two complex numbers are the same iff the real and imaginary
-- parts are the same
lemma ext_iff {z w : ℚ[i]} : z = w ↔ z.re = w.re ∧ z.im = w.im
  := by
  constructor
  · intro h
    simp [h]
  · intro ⟨h1, h2⟩
    ext
    · exact h1
    · exact h2




/-
 special elements in complexQ
-/

-- Define the numeral 0 explicitly
instance : OfNat complexQ 0 where
  ofNat := ⟨0, 0⟩

-- Define the numeral 1 explicitly
instance : OfNat complexQ 1 where
  ofNat := ⟨1, 0⟩

-- the complex number 0
def zero : ℚ[i] := ⟨0,0⟩

-- the complex number 0
def one : ℚ[i] := ⟨1,0⟩

-- the complex number i
def I : ℚ[i] := ⟨0,1⟩

-- ⟨0,0⟩ is the zero element
instance : Zero ℚ[i] := ⟨zero⟩

-- ⟨1,0⟩ is the unit
instance : One ℚ[i] := ⟨one⟩


#eval zero
#eval one
#eval I


/-
  Arithemtic operations
-/

instance : Add ℚ[i] :=
  ⟨fun x y ↦ ⟨ x.re + y.re, x.im + y.im⟩ ⟩

instance : Mul ℚ[i] :=
  ⟨fun x y ↦ ⟨ x.re*y.re - x.im*y.im, x.re*y.im + x.im*y.re⟩ ⟩

instance : Neg ℚ[i] :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

#eval -sample2

-- Subtraction will be defined in terms of addition and negative
-- The following two lines are redundant
--instance : Sub ℚ[i] :=
--   ⟨fun x y ↦ ⟨ x.re - y.re, x.im - y.im⟩ ⟩


#eval sample2 + I   -- 0 + -2*I
#eval sample3*I   -- 3 + 0*I


-- Some properties that are true by definition

@[simp] lemma zero_re : (0:ℚ[i]).re = 0 := rfl
@[simp] lemma zero_im : (0:ℚ[i]).im = 0 := rfl

@[simp] lemma one_re : (1:ℚ[i]).re = 1 := rfl
@[simp] lemma one_im : (1:ℚ[i]).im = 0 := rfl

@[simp] lemma add_re (x y : ℚ[i]) : (x+y).re = x.re+y.re := rfl
@[simp] lemma add_im (x y : ℚ[i]) : (x+y).im = x.im+y.im := rfl

@[simp]  lemma neg_re (x : ℚ[i]) : (-x).re = -x.re := rfl
@[simp] lemma neg_im (x : ℚ[i]) : (-x).im = -x.im := rfl

@[simp] lemma mul_re (x y: ℚ[i]) : (x*y).re = x.re*y.re - x.im*y.im := rfl
@[simp] lemma mul_im (x y: ℚ[i]) : (x*y).im = x.re*y.im + x.im*y.re := rfl

@[simp] lemma zero_def : (0 : ℚ[i]) = ⟨0,0⟩ := rfl
@[simp] lemma one_def : (1 : ℚ[i]) = ⟨1,0⟩ := rfl

@[simp] lemma I_re : I.re = 0 := rfl
@[simp] lemma I_im : I.im = 1 := rfl

@[simp] lemma I_mul_I : I*I = -1 :=
  ext_iff.mpr <| by simp

theorem I_mul (z:ℚ[i]) : I*z = ⟨ -z.im, z.re⟩ :=
  ext_iff.mpr <| by simp

-- mt stands for modus tollens
@[simp] lemma I_ne_zero : (I:ℚ[i]) ≠ 0 :=
  mt (congr_arg (fun z:ℚ[i] => z.im)) zero_ne_one.symm



@[simp]
theorem eta : ∀ z : complexQ, complexQ.mk z.re z.im = z := by
  intro z
  cases' z with x y
  dsimp

-- `ℚ[i]` is equivalent to `ℚ × ℚ`
@[simps apply]
def equivRationalProd : ℚ[i] ≃ ℚ×ℚ where
  toFun z := ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨ _, _ ⟩  => rfl
  right_inv := fun ⟨ _, _ ⟩  => rfl

theorem ext : ∀ {z w : ℚ[i]}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

attribute [local ext] complexQ.ext



-------------------------------------------
--  Coersion
-------------------------------------------

-- Every rational number can be regarded as a number in ℚ[i]
-- Rational number r is identified with the complex number ⟨r,0⟩

@[coe]
def ofRational (r: ℚ) : ℚ[i] := ⟨r,0⟩

instance : Coe ℚ ℚ[i] := ⟨ofRational⟩

#eval sample1 + (3 : ℚ)


def sample6 := complexQ.mk 5 0

-- The complex number 5+0i is the same as rational number 5
example : sample6 = (5:ℚ) := by rfl


@[simp, norm_cast]
lemma ofRational_re (r: ℚ)  : (r:ℚ[i]).re = r := rfl

@[simp, norm_cast]
lemma ofRational_im (r: ℚ)  : (r:ℚ[i]).im = 0 := rfl

@[simp, norm_cast]
lemma ofRational_inj {r s : ℚ} :
   (r : ℚ[i]) = s ↔ r = s := by
  constructor
  · intro h
    have h1: (ofRational r).re = (ofRational s).re := by
      congr
    rw [ofRational_re r] at h1
    rw [ofRational_re s] at h1
    exact h1
  · intro h
    congr

@[simp]
lemma ofRational_def (r:ℚ) : (complexQ.mk r 0) = (r:ℚ[i]) := by
  rfl

@[simp]
lemma rational_eq_coe' (r:ℚ) : r = (r : ℚ[i]) := by rfl


example (r s : ℚ) (h: (r:ℚ[i])=s) : r = s := by
  exact ofRational_inj.mp h

@[simp, norm_cast]
lemma ofRational_zero : ((0:ℚ) : ℚ[i]) = 0 := rfl


@[simp]
lemma ofRational_eq_zero {z:ℚ} : (z:ℚ[i]) = 0 ↔ z=0 :=
  ofRational_inj

lemma ofRational_ne_zero {z:ℚ} : (z:ℚ[i])≠ 0 ↔ z≠0 :=
  not_congr ofRational_eq_zero

@[simp]
lemma ofRational_eq_one {z:ℚ} : (z:ℚ[i]) = 1 ↔ z=1 :=
  ofRational_inj

lemma ofRational_ne_one {z:ℚ} : (z:ℚ[i]) ≠ 1 ↔ z ≠ 1 :=
  not_congr ofRational_eq_one

@[simp, norm_cast]
theorem ofRational_neg (r : ℚ) : ((-r : ℚ) : ℚ[i]) = -r := by
  apply ext_iff.mpr
  simp



lemma ofRational_add (r s : ℚ) : ( (r+s :ℚ) : ℚ[i]) = r+s := by
  refine ext_iff.2 ?_
  constructor
  · simp [ofRational_re]
  · simp [ofRational_im]

@[simp, norm_cast]
theorem ofRational_mul (r s : ℚ) : ((r * s : ℚ) : ℚ[i]) = r * s := by
  apply ext_iff.mpr
  constructor
  repeat dsimp <;> 
  simp [mul_zero, sub_zero]

theorem re_ofRational_mul (r : ℚ) (z : ℚ[i])
  : (r * z).re = r * z.re := by
  dsimp  
  simp only [zero_mul, sub_zero]

theorem im_ofRational_mul (r : ℚ) (z : ℚ[i])
  : (r * z).im = r * z.im := by
  dsimp
  simp only [zero_mul, add_zero]

lemma re_mul_ofRational (z : ℚ[i]) (r : ℚ)
  : (z * r).re = z.re *  r := by dsimp; simp only [mul_zero, sub_zero] 

lemma im_mul_ofRational (z : ℚ[i]) (r : ℚ)
  : (z * r).im = z.im *  r := by dsimp; simp only [mul_zero, zero_add]

@[simp]
theorem ofRational_mul' (r : ℚ) (z : ℚ[i]) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (re_ofRational_mul _ _) (im_ofRational_mul _ _)

theorem mk_eq_add_mul_I (a b : ℚ) : (complexQ.mk a b) = a + b * I :=
  ext_iff.2 <| by dsimp ; simp only 
    [mul_zero, mul_one, sub_self, add_zero, zero_add, and_self]

@[simp]
theorem re_add_im (z : ℚ[i]) : (z.re : ℚ[i]) + z.im * I = z :=
  ext_iff.2 <| by dsimp ; simp only [mul_zero, mul_one, sub_self, add_zero, zero_add, and_self]

theorem mul_I_re (z : ℚ[i]) : (z * I).re = -z.im := by simp

theorem mul_I_im (z : ℚ[i]) : (z * I).im = z.re := by simp

theorem I_mul_re (z : ℚ[i]) : (I * z).re = -z.im := by simp

theorem I_mul_im (z : ℚ[i]) : (I * z).im = z.re := by simp




-- Prove that 0 ≠ 1 in ℚ[i]
instance : Nontrivial ℚ[i] := by
  use 0, 1
  refine (ofRational_ne_one).mpr ?_
  norm_num



-----------------------------------------
--  Scalar multiplication
-----------------------------------------

namespace SMul

-- extend scalar multiplication on ℚ to scaloar multiplication on ℚ[i]
scoped instance instSMulRationalComplex {R : Type*} [SMul R ℚ] : SMul R ℚ[i] where
  smul r x := ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩

end SMul

open scoped SMul

section SMul

variable {R : Type*} [SMul R ℚ]

theorem smul_re (r : R) (z : ℚ[i])
  : (r • z).re = r • z.re := by simp [(· • ·), SMul.smul]

theorem smul_im (r : R) (z : ℚ[i])
  : (r • z).im = r • z.im := by simp [(· • ·), SMul.smul]

@[simp]
theorem rational_smul {x : ℚ} {z : ℚ[i]} : x • z = x * z :=
  rfl

end SMul





---------------------------------------
--  Q[i] as an additive group
---------------------------------------

-- the additive group of ℚ[i]

instance addCommGroup : AddCommGroup ℚ[i] where
  zero := (0:ℚ[i])
  add := Add.add
  -- sub := Sub.sub
  neg := Neg.neg
  nsmul := fun n z => n • z
  zsmul := fun n z => n • z
  add_assoc := by
    intros ;  ext <;> simp [add_assoc]
  zero_add := by
    intro a; ext
    · rw [add_re 0 a, zero_re]
      simp [zero_add]
    · rw [add_im 0 a, zero_im]
      simp [zero_add]
  add_zero := by
    intro a; ext
    · rw [add_re a 0, zero_re]
      simp [add_zero]
    · rw [add_im a 0, zero_im]
      simp [add_zero]
  add_comm := by
    intros a b
    ext
    · rw [add_re a b, add_re b a]
      ring
    · rw [add_im a b, add_im b a]
      ring
  neg_add_cancel := by
    intro a
    ext
    · rw [add_re (-a) a, neg_re a, zero_def]
      ring
    · rw [add_im (-a) a, neg_im a, zero_def]
      ring
  zsmul_zero' := by
    intro ; ext <;> dsimp <;> simp [smul_re, smul_im]
  nsmul_zero := by
    intro ; ext <;> dsimp <;> simp [smul_re, smul_im]
  nsmul_succ := by
   intros; ext <;> simp [add_mul, add_comm,
        smul_re, smul_im]
  zsmul_succ' := by
    intros; ext <;> simp [add_mul, add_comm,
      smul_re, smul_im]
  zsmul_neg' := by
    intros; ext <;> simp [add_mul, smul_re, smul_im]


-- After verifying that the additive group structure,
-- we can now do subtraction
#eval sample1 - sample3

instance : One complexQ where
  one := ⟨1, 0⟩

-- Casting from `ℕ` and `ℤ` to `ℚ[i]`

instance addGroupWithOne : AddGroupWithOne complexQ where
  -- 1. Automatically inherit AddGroup from your previously defined AddCommGroup
  toAddGroup := inferInstance
  
  -- 2. Explicitly construct the '1' element
  one := ⟨1, 0⟩
  
  -- 3. Explicitly state the typecast to ℚ
  natCast n := ⟨(n : ℚ), 0⟩
  natCast_zero := by
    ext
    · exact Nat.cast_zero
    · rfl
  natCast_succ n := by
    push_cast
    ext
    · -- Solves the real part: ↑(n + 1) = ↑n + 1
      rfl
    · -- Solves the imaginary part: 0 = complexQ.im 1
      push_cast
      simp
          
  intCast n := ⟨(n : ℚ), 0⟩
  intCast_ofNat n := by
    ext
    · push_cast; rfl
    · rfl
  intCast_negSucc n := by
    ext
    · push_cast
      grind [neg_re]
    · rfl


-- Multiplication by integers are now enabled
#eval 4 * sample1
#eval (-2) * sample2


-- `ℚ[i]` is a communtative ring with identity

instance commRing : CommRing ℚ[i] := {
  addGroupWithOne with
  mul := (· * ·)
  npow := @npowRec _ ⟨(1 : ℚ[i])⟩ ⟨(· * ·)⟩
  add_comm := by intros; ext <;> simp [add_comm]
  left_distrib := by
    intros; ext <;> simp [mul_re, mul_im] <;> ring
  right_distrib := by
    intros; ext <;> simp [mul_re, mul_im] <;> ring
  zero_mul := by intros; ext <;> dsimp <;> simp [zero_mul]
  mul_zero := by intros; ext <;> dsimp <;> simp [mul_zero]
  mul_assoc := by intros; ext <;> simp only [mul_re, mul_im] <;> ring
  one_mul := by 
    intros; 
    ext <;> simp
  mul_one := by intros; ext <;> simp
  mul_comm := by intros; ext <;> simp [mul_comm]; ring
}



instance : Ring ℚ[i] := by infer_instance
instance : CommSemiring ℚ[i] := by infer_instance
instance : Semiring ℚ[i] := by infer_instance




-------------------------------------------
--   Complex conjugation
-------------------------------------------

-- conjugation in ℚ[i] is the ring endomorphism in a StarRing

instance : StarRing ℚ[i] where
  star z := ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

-- One we have set up ℚ[i] as a StarRing,
-- the conjugation function `starRingEnd ℚ[i]` can be invoked
-- by `conj` in the namespace `ComplexConjugate`

open ComplexConjugate

-- notation "conj" => (starRingEnd ℂ)

@[simp]
lemma conj_re (z : ℚ[i]) : (conj z).re = z.re := rfl

@[simp]
lemma conj_im (z : ℚ[i]) : (conj z).im = -z.im := rfl

theorem conj_ofReal (r : ℚ) : conj (r : ℚ[i]) = r :=
  ext_iff.mpr <| by simp

@[simp]
lemma conj_I : conj I = -I := by
  exact rfl

theorem conj_natCast (n : ℕ) : conj (n : ℚ[i]) = n := map_natCast _ _

theorem conj_ofNat (n : ℕ) [n.AtLeastTwo]
    : conj (no_index (OfNat.ofNat n : ℚ[i])) = OfNat.ofNat n :=
  map_ofNat _ _

theorem conj_neg_I : conj (-I) = I :=
  ext_iff.2 <| by simp



theorem conj_eq_iff_real {z : ℚ[i]} : conj z = z ↔ ∃ r : ℚ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <|
    eq_zero_of_neg_eq (congr_arg (fun z:ℚ[i]=> z.im) h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_ofReal]⟩


@[simp]
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl


---------------------------------------------
--  Norm square function
---------------------------------------------


@[pp_nodot]
def normSq : ℚ[i]  →*₀ ℚ  where
  toFun z := z.re * z.re + z.im * z.im
  map_zero' := by dsimp; simp
  map_one' := by simp [one_def, ofRational_def, 
  ofRational_re, mul_one, ofRational_im, mul_zero, add_zero]
  map_mul' z w := by simp; ring

theorem normSq_apply (z : ℚ[i]) : normSq z = z.re * z.re + z.im * z.im :=
  rfl

@[simp]
theorem normSq_ofRational (r : ℚ) : normSq r = r * r := by
  simp [normSq]

@[simp]
theorem normSq_natCast (n : ℕ) : normSq n = n * n := normSq_ofRational _

@[simp]
theorem normSq_intCast (z : ℤ) : normSq z = z * z := normSq_ofRational _

@[simp]
theorem normSq_ofNat (n : ℕ) [n.AtLeastTwo] :
    normSq (no_index (OfNat.ofNat n : ℚ[i])) = OfNat.ofNat n * OfNat.ofNat n
    :=  normSq_natCast _

@[simp]
theorem normSq_mk (x y : ℚ) : normSq ⟨x,y⟩  = x*x + y*y := rfl

theorem normSq_add_mul_I (x y : ℚ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, normSq_mk, sq, sq]

theorem normSq_eq_conj_mul_self {z : ℚ} : (normSq z : ℚ[i]) = conj z * z := by
  ext
  repeat dsimp ; simp [normSq]

theorem normSq_zero : normSq 0 = 0 := normSq.map_zero

theorem normSq_one : normSq 1 = 1 :=  normSq.map_one

theorem normSq_nonneg (z : ℚ[i]) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem normSq_eq_zero {z : ℚ[i]} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩

@[simp]
theorem normSq_pos {z : ℚ[i]}
  : 0 < normSq z ↔ z ≠ 0 :=
  (normSq_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans normSq_eq_zero)

@[simp]
theorem normSq_neg (z : ℚ[i]) : normSq (-z) = normSq z := by simp [normSq]

@[simp]
theorem normSq_conj (z : ℚ[i]) : normSq (conj z) = normSq z := by simp [normSq]

theorem normSq_mul (z w : ℚ[i]) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w

theorem normSq_add (z w : ℚ[i])
  : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  dsimp [normSq]; ring

theorem re_sq_le_normSq (z : ℚ[i]) : z.re * z.re ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

theorem im_sq_le_normSq (z : ℚ[i]) : z.im * z.im ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℚ[i]) : z * conj z = normSq z := by
  apply ext_iff.mpr
  dsimp ; simp [normSq]
  ring

theorem add_conj (z : ℚ[i]) : z + conj z = (2 * z.re : ℚ) := by
  apply ext_iff.mpr
  dsimp ; simp only [add_neg_cancel, and_true]
  ring


@[simp, norm_cast]
theorem ofRational_one : ((1 : ℚ) : ℚ[i]) = 1 := rfl

-- The coercion `ℚ  → ℚ[i]` is a ring homomorphism
-- The symbol `→+*` signifies that the mapping is a ring homomorphism
def ofRational' : ℚ →+* ℚ[i] where
  toFun x := (x : ℚ[i])
  map_one' := ofRational_one
  map_zero' := ofRational_zero
  map_mul' := ofRational_mul
  map_add' := ofRational_add

@[simp]
theorem ofRational_eq_coe (r : ℚ) : ofRational r = r := rfl

@[simp]
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp]
theorem I_pow_four : I ^ 4 = 1 := by
  rw [(by norm_num : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]

-- The next two theorems differs from the analog of the complex type in Mathlib
-- They are not true by definition, but require some proof.
@[simp]
theorem sub_re (z w : ℚ[i]) : (z - w).re = z.re - w.re := by
  rw [(by rfl : z-w  = z+(-w)), add_re, neg_re]
  ring

@[simp]
theorem sub_im (z w : ℚ[i]) : (z - w).im = z.im - w.im := by
  rw [(by rfl : z-w  = z+(-w)), add_im, neg_im]
  ring


@[simp, norm_cast]
theorem ofRational_sub (r s : ℚ) : ((r - s : ℚ) : ℚ[i]) = r - s := by
  apply ext_iff.mpr
  dsimp ; simp [sub_re, sub_im]

@[simp, norm_cast]
theorem ofRational_pow (r : ℚ) (n : ℕ)
  : ((r^n : ℚ) : ℚ[i]) = (r : ℚ[i])^n := by
  induction' n with n hn
  · rw [pow_zero, pow_zero]
    rfl
  · -- inductive step
    rw [pow_succ, ofRational_mul, hn]
    ring

theorem sub_conj (z : ℚ[i]) : z - conj z = (2 * z.im : ℚ) * I := by
  apply ext_iff.mpr
  dsimp ; simp
  ring

theorem normSq_sub (z w : ℚ[i])
  : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg]
  rw [normSq_add]
  simp
  ring



-------------------------------------------
--   Inversion
-------------------------------------------

-- Definition of multiplicative inverse
instance : Inv ℚ[i] :=
  ⟨fun z => conj z * ((normSq z)⁻¹ : ℚ)⟩


theorem inv_def (z : ℚ[i]) : z⁻¹ = conj z * ((normSq z)⁻¹ : ℚ) :=
  rfl

@[simp]
theorem inv_re (z : ℚ[i])  : z⁻¹.re = z.re / normSq z := by
  simp [inv_def, division_def]

@[simp]
theorem inv_im (z : ℚ[i]) : z⁻¹.im = -z.im / normSq z := by
  simp [inv_def, division_def]

@[simp, norm_cast]
theorem ofRational_inv (r : ℚ) : ((r⁻¹ : ℚ) : ℚ[i]) = (r : ℚ[i])⁻¹ := by
  apply ext_iff.2
  simp [normSq]

protected theorem complexQ.inv_zero : (0⁻¹ : ℚ[i]) = 0 := by
  rw [← ofRational_zero]
  rw [← ofRational_inv]
  rw [inv_zero]

protected theorem complexQ.mul_inv_cancel {z : ℚ[i]} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def]
  rw [← mul_assoc]
  rw [mul_conj]
  rw [← ofRational_mul]
  norm_cast
  exact mul_inv_cancel₀ (mt normSq_eq_zero.1 h)



-- an instance of monoid with inverse and division
-- After ths point we can use the division operator

instance instDivInvMonoid : DivInvMonoid ℚ[i] where

#eval (2-I)/(1-I)

-- relation between division and the real part and imaginary part

lemma div_re (z w : ℚ[i])
  : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]

lemma div_im (z w : ℚ[i])
  : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]




-------------------------------------
--  Cast lemmas
-------------------------------------

instance instNNRatCast : NNRatCast ℚ[i] where nnratCast q := ofRational q
instance instRatCast : RatCast ℚ[i] where ratCast q := ofRational q

@[simp, norm_cast] lemma ofRational_ofNat (n : ℕ) [n.AtLeastTwo] :
    ofRational (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl

@[simp, norm_cast] lemma ofRational_natCast (n : ℕ) : ofRational n = n := rfl

@[simp, norm_cast] lemma ofRational_intCast (n : ℤ) : ofRational n = n := rfl

@[simp, norm_cast] lemma ofRational_nnratCast (q : ℚ≥0) : ofRational q = q := rfl

@[simp] lemma ofRational_ratCast (q : ℚ) : ofRational q = q := rfl


@[simp] lemma re_ofNat (n : ℕ) [n.AtLeastTwo]
  : (no_index (OfNat.ofNat n) : ℚ[i]).re = OfNat.ofNat n := rfl

@[simp] lemma im_ofNat (n : ℕ) [n.AtLeastTwo]
   : (no_index (OfNat.ofNat n) : ℚ[i]).im = 0 := rfl

@[simp, norm_cast] lemma natCast_re (n : ℕ) : (n : ℚ[i]).re = n := rfl

@[simp, norm_cast] lemma natCast_im (n : ℕ) : (n : ℚ[i]).im = 0 := rfl

@[simp, norm_cast] lemma intCast_re (n : ℤ) : (n : ℚ[i]).re = n := rfl

@[simp, norm_cast] lemma intCast_im (n : ℤ) : (n : ℚ[i]).im = 0 := rfl

@[simp, norm_cast] lemma re_nnratCast (q : ℚ≥0) : (q : ℚ[i]).re = q := rfl

@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : ℚ[i]).im = 0 := rfl

@[simp, norm_cast] lemma ratCast_re (q : ℚ) : (q : ℚ[i]).re = q := rfl

@[simp, norm_cast] lemma ratCast_im (q : ℚ) : (q : ℚ[i]).im = 0 := rfl



lemma ofRational_nsmul (n : ℕ) (r : ℚ)
  : ↑(n • r) = n • (r : ℚ[i]) := by
  simp
  refine ext_iff.mpr ?_
  constructor
  · dsimp
    ring
  · simp



lemma ofRational_zsmul (n : ℤ) (r : ℚ) : ↑(n • r) = n • (r : ℚ[i]) := by
  simp
  refine ext_iff.mpr ?_
  constructor
  · dsimp
    ring
  · simp




------------------------------------------
--  ℚ[i] is a field
------------------------------------------

instance instField : Field ℚ[i] where
  mul_inv_cancel := fun z hz => complexQ.mul_inv_cancel hz
  inv_zero := complexQ.inv_zero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  qsmul_def q z := ext_iff.2 <| by simp
  ratCast_def q := by
    ext
    · simp only [ratCast_re]
      simp [div_re]
      simp [mul_div_mul_comm]
      exact (Rat.num_div_den q).symm
    · simp only [ratCast_im]
      simp [div_im]
  nnqsmul_def n z :=
    ext_iff.2 <| by simp [NNRat.smul_def, smul_re, smul_im]
  nnratCast_def q := by ext <;> simp [NNRat.cast_def, div_re, div_im, mul_div_mul_comm]

@[simp, norm_cast]
lemma ofReal_nnqsmul (q : ℚ≥0) (r : ℚ) : ofRational (q • r) = q • r := by
    ext
    repeat simp[NNRat.smul_def]


@[simp, norm_cast]
lemma ofReal_qsmul (q : ℚ) (r : ℚ) : ofRational (q • r) = q • r := by
  ext
  repeat simp [smul_eq_mul, ofRational_ratCast, ratCast_re,
    rational_smul, mul_re, ratCast_im,
    mul_zero, sub_zero]


theorem conj_inv (x : ℚ[i]) : conj x⁻¹ = (conj x)⁻¹ := by
  simp only [map_inv₀]


@[simp, norm_cast]
theorem ofRational_div (r s : ℚ) : ((r / s : ℚ) : ℚ[i]) = r / s :=
  map_div₀ ofRational' r s


@[simp, norm_cast]
theorem ofReal_zpow (r : ℚ) (n : ℤ) : ((r ^ n : ℚ) : ℚ[i]) = (r : ℚ[i]) ^ n :=
  map_zpow₀ ofRational' r n

@[simp]
theorem div_I (z : ℚ[i]) : z / I = -(z * I) := by
  apply (div_eq_iff_mul_eq I_ne_zero).2
  simp 
  calc
    -(z * I * I) = -(z*(I*I)) := by ring
               _ = -(z*(-1)) := by rw [I_mul_I]
               _ = z := by ring


@[simp]
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div, div_I, one_mul]

theorem normSq_inv (z : ℚ[i]) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z

theorem normSq_div (z w : ℚ[i]) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w

lemma div_ofRational (z : ℚ[i]) (x : ℚ) : z / x = ⟨z.re / x, z.im / x⟩ := by
  simp [div_eq_inv_mul]
  apply ext_iff.2
  simp
  constructor
  repeat left ; simp[normSq]

lemma div_natCast (z : ℚ[i]) (n : ℕ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofRational z n

lemma div_intCast (z : ℚ[i]) (n : ℤ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofRational z n

lemma div_ratCast (z : ℚ[i]) (x : ℚ) : z / x = ⟨z.re / x, z.im / x⟩ :=
  mod_cast div_ofRational z x

lemma div_ofNat (z : ℚ[i]) (n : ℕ) [n.AtLeastTwo] :
    z / OfNat.ofNat n = ⟨z.re / OfNat.ofNat n, z.im / OfNat.ofNat n⟩ :=
  div_natCast z n

@[simp] lemma div_ofReal_re (z : ℚ[i]) (x : ℚ) : (z / x).re = z.re / x := by
  rw [div_ofRational]

@[simp] lemma div_ofReal_im (z : ℚ[i]) (x : ℚ) : (z / x).im = z.im / x := by
  rw [div_ofRational]

@[simp] lemma div_natCast_re (z : ℚ[i]) (n : ℕ) : (z / n).re = z.re / n := by
  rw [div_natCast]

@[simp] lemma div_natCast_im (z : ℚ[i]) (n : ℕ) : (z / n).im = z.im / n := by
  rw [div_natCast]

@[simp] lemma div_intCast_re (z : ℚ[i]) (n : ℤ) : (z / n).re = z.re / n := by
  rw [div_intCast]

@[simp] lemma div_intCast_im (z : ℚ[i]) (n : ℤ) : (z / n).im = z.im / n := by
  rw [div_intCast]

@[simp] lemma div_ratCast_re (z : ℚ[i]) (x : ℚ) : (z / x).re = z.re / x := by
  rw [div_ratCast]

@[simp] lemma div_ratCast_im (z : ℚ[i]) (x : ℚ) : (z / x).im = z.im / x := by
  rw [div_ratCast]

@[simp]
lemma div_ofNat_re (z : ℚ[i]) (n : ℕ) [n.AtLeastTwo] :
    (z / no_index (OfNat.ofNat n)).re = z.re / OfNat.ofNat n := div_natCast_re z n

@[simp]
lemma div_ofNat_im (z : ℚ[i]) (n : ℕ) [n.AtLeastTwo] :
    (z / no_index (OfNat.ofNat n)).im = z.im / OfNat.ofNat n := div_natCast_im z n


-- Characteristic 0
instance instCharZero : CharZero ℚ[i] :=
  charZero_of_inj_zero fun n h => by rwa [← ofRational_natCast, ofRational_eq_zero, Nat.cast_eq_zero] at h

-- Real part of a complex number z equals the sum of z and conj z divided by 2
theorem re_eq_add_conj (z : ℚ[i]) : (z.re : ℚ) = (z + conj z) / 2 := by
  rw [add_conj]
  rw [ofRational_mul]
  simp [mul_div_cancel_left₀ (z.re : ℚ[i]) two_ne_zero]

-- Imaginary part of a complex number z equals the difference of z and conj z divided by 2i
theorem im_eq_add_conj (z : ℚ[i]) : (z.im : ℚ) = (z - conj z) / (I*2) := by
  rw [sub_conj]
  rw [ofRational_mul]
  rw [mul_comm]
  rw [← mul_assoc]
  push_cast
  rw [mul_div_cancel_left₀ _ ?_]
  · rfl
  · norm_num

-- a random calculation
#eval 2*((2-I)*(2+I/6)/(I*5/3) + 5/2)

#eval normSq (2+2*I/4)*I*I




-- Tree problem
/- In the island there are only 2 trees, A and B, and the remnants of a hanging place.

Start at the hanging place and count the steps to go in a straight
line to tree A. When you arrive, turn 90º to the left and walk the
same amount of steps. Where you stopped, place a mark on the ground, and call this point A'

Go back to the hanging place and count the steps to tree B, also in a
straight line.  When there, turn 90º to the right and walk the same
amount of steps forward and place a mark on the ground. This is point B'

Bury the treasure box at the mid-point of A' and B'.

-- H : Hanging place
-- A : tree A
-- B : tree B
-- A': the first mark on the ground
-- B': the second mark
-- T : Location of the treasure box
-/

-- Prove that we can find the location of the treasure box even if
-- the hanging place disappeared in the island.
-- Show that the location of the treasure box does not depend on the
-- location of the hanging place
example  {H A B A' B' T: ℚ[i]}
  (h1 : A' = A+I*(A-H) )  (h2 : B' = B-I*(B-H) )
  (h3 : T = (A'+B')/2 )
    : T = (A+B)/2+ I*(A-B)/2 := by
  rw [h3, h2, h1]
  ring


end complex_number_game
