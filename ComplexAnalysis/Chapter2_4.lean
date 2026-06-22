/-

  Three-point mapping property of
  linear fractional transformation

-/

import Mathlib.Tactic
import ComplexAnalysis.Chapter2_2
import ComplexAnalysis.Chapter2_3

open EComplex LinearFracTrans

section ThreePointsProperty

/-
Lemma preparing for prove exist LFT mapping three distinct
 point to three other distinct point
-/

/-- construct lft, such that z1 ↦ 0 , z2 ↦ 1 ,z3 ↦ ∞
-/
def construct_lft_to0_1_infty (z1 z2 z3 : EComplex)
  (hz : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z3 ≠ z1) : LinearFracTrans :=
  match z1 , z2 , z3 with
  | ∞ , EComplex.some z2 , EComplex.some z3 => { a := 0 , b := z2 - z3, c := 1 , d := -z3 , determinant_ne_zero := by {
      simp only [mul_neg, zero_mul, neg_zero, mul_one, zero_sub, neg_sub, ne_eq]
      push Not
      rcases hz with ⟨h1,h2,h3⟩
      apply sub_ne_zero.2
      exact EComplex.coe_ne_coe_iff.mp (_root_.id (Ne.symm h2))
       }}
  | EComplex.some z1 , ∞ , EComplex.some z3 => {a := 1 , b := - z1 , c := 1 , d := - z3 , determinant_ne_zero := by {
    simp only [mul_neg, one_mul, mul_one, sub_neg_eq_add, ne_eq]
    push Not
    rcases hz with ⟨h1,h2,h3⟩
    rw [neg_add_eq_sub]
    apply sub_ne_zero.2
    exact EComplex.coe_ne_coe_iff.mp (_root_.id (Ne.symm h3))
    }}
  | EComplex.some z1 ,EComplex.some z2 , ∞ => {a := 1 , b := - z1 , c := 0 , d :=  z2 - z1 , determinant_ne_zero := by {
    simp only [one_mul, mul_zero, sub_zero, ne_eq]
    push Not
    apply sub_ne_zero.2
    rcases hz with ⟨h1,h2,h3⟩
    exact EComplex.coe_ne_coe_iff.mp (_root_.id (Ne.symm h1))
  }}
  | EComplex.some z1 , EComplex.some z2 , EComplex.some z3 => {a := z2 - z3, b :=   -z1 * (z2 - z3) , c := z2 - z1, d :=  -z3 * (z2 -z1) , determinant_ne_zero := by {
    simp only [neg_mul, mul_neg, sub_neg_eq_add, ne_eq]
    push Not
    rcases hz with ⟨h1,h2,h3⟩
    have hsimp : -((z2 - z3) * (z3 * (z2 - z1))) + z1 * (z2 - z3) * (z2 - z1)  = (z1 - z2) * (z2 - z3) * (z3 - z1) := by ring
    rw [hsimp]
    have h12 : z1 - z2 ≠ 0 := by exact sub_ne_zero_of_ne fun a => h1 (congrArg EComplex.some a)
    have h23 : z2 - z3 ≠ 0 := by exact sub_ne_zero_of_ne fun a => h2 (congrArg EComplex.some a)
    have h31 : z3 - z1 ≠ 0 := by exact sub_ne_zero_of_ne fun a => h3 (congrArg EComplex.some a)
    apply mul_ne_zero
    apply mul_ne_zero
    assumption
    assumption
    assumption
  }}



/--  #### Theorem 2.4.2
  proving that constructed lft actually maps z1 z2 z3 to 0 1 ∞
-/
theorem constructlft_map_to_01infty
  (z1 z2 z3 : EComplex) (hz : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z3 ≠ z1) :
  (construct_lft_to0_1_infty z1 z2 z3 hz) z1
  = EComplex.some 0 ∧
  (construct_lft_to0_1_infty z1 z2 z3 hz) z2
  = EComplex.some 1 ∧
  (construct_lft_to0_1_infty z1 z2 z3 hz) z3
  = ∞ := by
    let f := construct_lft_to0_1_infty z1 z2 z3 hz
    have hf : construct_lft_to0_1_infty z1 z2 z3 hz = f := by rfl
    rw [hf]
    cases z1 with
    | none => {
      cases z2 with
      | none => {
        cases z3 with
        | none => {
          contradiction
        }
        | some z3 => {
          rcases hz with ⟨h1,h2,h3⟩
          contradiction
        }
      }
      | some z2 => {
        cases z3 with
        | none => {
          rcases hz with ⟨h1,h2,h3⟩
          contradiction
        }
        | some z3 => {
          rcases hz with ⟨h1,h2,h3⟩
          rw [← hf]
          unfold construct_lft_to0_1_infty
          simp only [ne_eq, one_ne_zero, not_false_eq_true, f_infty_a_div_c]
          unfold LinearFracTrans.apply
          simp only [one_ne_zero, ↓reduceIte, neg_neg, div_one, zero_mul, zero_add, one_mul,
            and_true]
          constructor
          change EComplex.div ↑0 ↑1 = EComplex.some 0
          unfold EComplex.div
          unfold EComplex.inv
          simp only [one_ne_zero, ↓reduceIte, inv_one]
          change EComplex.mul ↑0 ↑1 = EComplex.some 0
          unfold EComplex.mul
          simp only [mul_one]
          have h23_not_eql : z2 ≠ z3 := by exact EComplex.coe_ne_coe_iff.mp h2
          split_ifs
          contradiction
          rw [← sub_eq_add_neg]
          have fraction_eq1 : (z2 - z3) / (z2 - z3) = 1 := by {
            apply div_self
            (expose_names; exact sub_ne_zero_of_ne h)
          }
          rw [fraction_eq1]
        }
      }
    }
    | some z1 => {
      cases z2 with
      | none => {
        cases z3 with
        | none => {
          rcases hz with ⟨h1,h2,h3⟩
          contradiction
        }
        | some z3 => {
          rcases hz with ⟨h1,h2,h3⟩
          rw [← hf]
          unfold construct_lft_to0_1_infty
          simp only [ne_eq, one_ne_zero, not_false_eq_true, f_infty_a_div_c]
          unfold LinearFracTrans.apply
          simp only [one_ne_zero, ↓reduceIte, neg_neg, div_one, one_mul, add_neg_cancel, zero_div,
            ite_eq_right_iff, reduceCtorEq, imp_false, and_true]
          constructor
          push Not
          exact EComplex.coe_ne_coe_iff.mp (_root_.id (Ne.symm h3))
          change EComplex.div ↑1 ↑1 = EComplex.some 1
          unfold EComplex.div
          unfold EComplex.inv
          simp only [one_ne_zero, ↓reduceIte, inv_one]
          change EComplex.mul ↑1 ↑1 = EComplex.some 1
          unfold EComplex.mul
          simp
        }
      }
      | some z2 => {
        cases z3 with
        | none => {
          rcases hz with ⟨h1,h2,h3⟩
          rw [← hf]
          have h12_not_eql : z2 - z1 ≠ 0 := by {
            exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
          }
          unfold construct_lft_to0_1_infty
          simp only [f_infty_infty, and_true]
          unfold LinearFracTrans.apply
          simp
          constructor
          field_simp
          simp
          field_simp
          rw [← sub_eq_add_neg]
        }
        | some z3 => {
          rcases hz with ⟨h1,h2,h3⟩
          rw [← hf]
          unfold construct_lft_to0_1_infty
          unfold LinearFracTrans.apply
          have h12 : z1 ≠ z2 := by exact fun a => h1 (congrArg Option.some a)
          have h23 : z2 ≠ z3 := by exact fun a => h2 (congrArg Option.some a)
          have h13 : z1 ≠ z3 := by exact EComplex.coe_ne_coe_iff.mp (_root_.id (Ne.symm h3))
          simp
          have h12_not0 : z2 -z1 ≠ 0 := by exact sub_ne_zero_of_ne (_root_.id (Ne.symm h12))
          have h23_not0 : z2 -z3 ≠ 0 := by exact sub_ne_zero_of_ne h23
          have h31_not0 : z3 -z1 ≠ 0 := by exact sub_ne_zero_of_ne (_root_.id (Ne.symm h13))
          simp [h12_not0,h23,h13]
          constructor
          have h123 : (z2 - z3) * z1 + -(z1 * (z2 - z3)) = 0 := by ring
          rw [h123]
          field_simp
          · exact Or.inl trivial
          · have hden : (z2 - z1) * z2 + -(z3 * (z2 - z1)) ≠ 0 := by
                have hfactor :
                  (z2 - z1) * z2 + -(z3 * (z2 - z1))
                  = (z2 - z1) * (z2 - z3) := by ring
                rw [hfactor]
                exact mul_ne_zero h12_not0 h23_not0
            have hnum_eq_den :
              (z2 - z3) * z2 + -(z1 * (z2 - z3))
              = (z2 - z1) * z2 + -(z3 * (z2 - z1)) := by ring
            calc
              ((z2 - z3) * z2 + -(z1 * (z2 - z3))) /
                ((z2 - z1) * z2 + -(z3 * (z2 - z1)))
                =
                ((z2 - z1) * z2 + -(z3 * (z2 - z1))) /
                ((z2 - z1) * z2 + -(z3 * (z2 - z1))) := by
                  rw [hnum_eq_den]
            _ = 1 := by exact div_self hden
          }
        }
    }


/-- prove inverse lft map 0,1,∞ to w1 w2 w3 -/
theorem proof_inv_constructlft_map_to_01infty
  (w1 w2 w3 : EComplex) (hw : w1 ≠ w2 ∧ w2 ≠ w3 ∧ w3 ≠ w1) :
  LinearFracTrans.inv (construct_lft_to0_1_infty w1 w2 w3 hw)
  (EComplex.some 0) = w1 ∧
  LinearFracTrans.inv (construct_lft_to0_1_infty w1 w2 w3 hw)
  (EComplex.some 1) = w2 ∧
  LinearFracTrans.inv (construct_lft_to0_1_infty w1 w2 w3 hw) ∞
  = w3 := by
    let g := LinearFracTrans.inv (construct_lft_to0_1_infty w1 w2 w3 hw)
    have hg : LinearFracTrans.inv (construct_lft_to0_1_infty w1 w2 w3 hw) = g := by rfl
    unfold LinearFracTrans.apply
    unfold LinearFracTrans.inv
    unfold construct_lft_to0_1_infty
    rcases hw with ⟨h1,h2,h3⟩
    cases w1 with
    | none => {
      cases w2 with
      | none => {
        cases w3 with
        | none => {
          contradiction
        }
        | some w3 => {
          contradiction
        }
      }
      | some w2 => {
        cases w3 with
        | none => {
          contradiction
        }
        | some w3 => {
          simp only [mul_neg, zero_mul, neg_zero, mul_one, zero_sub, neg_sub, div_eq_zero_iff,
            neg_eq_zero, one_ne_zero, false_or, zero_div, div_zero, mul_zero, add_zero, ↓reduceIte,
            ite_eq_right_iff, reduceCtorEq, imp_false]
          constructor
          push Not
          exact sub_ne_zero_of_ne fun a ↦ h2 (congrArg EComplex.some (_root_.id (Eq.symm a)))
          constructor
          have h32_not0 : w3 - w2 ≠ 0 := by {
            exact sub_ne_zero_of_ne fun a ↦ h2 (congrArg EComplex.some (_root_.id (Eq.symm a)))
          }
          simp only [h32_not0, ↓reduceIte, ne_eq, not_false_eq_true, div_self]
          congr 1
          field_simp [h32_not0]
          ring
          have h32_not0 : w3 - w2 ≠ 0 := by {
            exact sub_ne_zero_of_ne fun a ↦ h2 (congrArg EComplex.some (_root_.id (Eq.symm a)))
          }
          simp only [h32_not0, ↓reduceIte]
          congr 1
          field_simp [h32_not0]
        }
      }
    }
    | some w1 => {
      cases w2 with
      | none => {
        cases w3 with
        | none => {
          contradiction
        }
        | some w3 => {
          simp only [mul_neg, one_mul, mul_one, sub_neg_eq_add, div_eq_zero_iff, neg_eq_zero,
            one_ne_zero, false_or, one_div, div_inv_eq_mul, mul_zero, neg_neg, zero_add]
          constructor
          have w31_not0 : -w3 + w1 ≠ 0 := by {
            rw [neg_add_eq_sub]
            rw [sub_ne_zero]
            exact EComplex.coe_ne_coe_iff.mp (_root_.id (Ne.symm h3))
          }
          simp [w31_not0]
          push Not
          field_simp
          exact zero_ne_one' ℂ
          constructor
          have w31_not0 : -w3 + w1 ≠ 0 := by {
            rw [neg_add_eq_sub]
            rw [sub_ne_zero]
            exact EComplex.coe_ne_coe_iff.mp (_root_.id (Ne.symm h3))
          }
          simp [w31_not0]
          field_simp
          have w31_not0 : -w3 + w1 ≠ 0 := by {
            rw [neg_add_eq_sub]
            rw [sub_ne_zero]
            exact EComplex.coe_ne_coe_iff.mp (_root_.id (Ne.symm h3))
          }
          simp only [w31_not0, ↓reduceIte]
          congr 1
          field_simp
        }
      }
      | some w2 => {
        cases w3 with
        | none => {
          simp
          constructor
          have w21_not0 : (w2 - w1) ≠ 0 := by {
            exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
          }
          field_simp
          have w21_not0 : (w2 - w1) ≠ 0 := by {
            exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
          }
          field_simp
          ring
        }
        | some w3 => {
          simp only [neg_sub, neg_mul, mul_neg, sub_neg_eq_add, div_eq_zero_iff, mul_zero, neg_neg,
            zero_add, mul_one]
          have h12_not0 : w1 - w2 ≠ 0 := by {
            exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some a)
          }
          have h23_not0 : w2 - w3 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h2 (congrArg EComplex.some a)
          }
          have h31_not0 : w3 - w1 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h3 (congrArg EComplex.some a)
          }
          have neg_h13_not0 : -w3 + w1 ≠ 0 := by {
              rw [neg_add_eq_sub]
              exact sub_ne_zero_of_ne fun a ↦ h3 (congrArg EComplex.some (_root_.id (Eq.symm a)))
          }
          have if_condiction2_false : -((w2 - w3) * (w3 * (w2 - w1))) + w1 * (w2 - w3) * (w2 - w1) ≠ 0 := by {
            intro h
            have factored : -((w2 - w3) * (w3 * (w2 - w1))) + w1 * (w2 - w3) * (w2 - w1)
              = (w2 - w3) * (w2 - w1) * (w1 - w3) := by ring
            rw [factored] at h
            simp only [mul_eq_zero] at h
            rcases h with htwo | h13
            rcases htwo with h23 | h13
            contradiction
            have contra_cond : w2 - w1 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
            }
            contradiction
            have contra_cond : w1 - w3 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h3 (congrArg EComplex.some (_root_.id (Eq.symm a)))
            }
            contradiction
          }
          simp only [h12_not0, if_condiction2_false, or_self, ↓reduceIte]
          constructor
          rw [if_neg]
          · {
            congr 1
            have h23_not0 : w2 - w3 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h2 (congrArg EComplex.some a)
            }
            have h21_not0 : w2 - w1 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
            }
            field_simp [h23_not0,h21_not0]
            }
          · {
            push Not
            field_simp
            have h21_not0 : w2 - w1 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
            }
            field_simp
            intro h
            field_simp at h
            rw [zero_mul] at h
            rw [zero_eq_neg] at h
            contradiction
            }
          constructor
          rw [if_neg]
          · {
            congr 1
            have h21_not0 : w2 - w1 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
            }
            have h13_not0 : w1 - w3 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h3 (congrArg EComplex.some (_root_.id (Eq.symm a)))
            }
            field_simp
            simp
            field_simp
            ring
            }
          · {
            push Not
            have h21_not0 : w2 - w1 ≠ 0 := by {
              exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
            }
            field_simp
            rw [neg_div']
            intro h
            field_simp at h
            rw [neg_sub,eq_sub_iff_add_eq,sub_add_cancel] at h
            exact Ne.elim h3 (congrArg EComplex.some (_root_.id (Eq.symm h)))
            }
          congr 1
          have h21_not0 : w2 - w1 ≠ 0 := by {
            exact sub_ne_zero_of_ne fun a ↦ h1 (congrArg EComplex.some (_root_.id (Eq.symm a)))
          }
          field_simp
          ring
        }
      }
    }



/--  #### Theorem 2.4.3 (existence part)
  Given any three distinct points z1, z2 and z3 and any three distinct
points w1, w2 and w3, all in the extended complex plane EComplex , there is a linear
fractional transformation that maps z1 to w1, z2 to w2, and z3 to w3
-/
theorem exists_lft_map_three_points (z1 z2 z3 w1 w2 w3 : EComplex)
   (hz : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z3 ≠ z1)
   (hw : w1 ≠ w2 ∧ w2 ≠ w3 ∧ w3 ≠ w1) :
 ∃ f : LinearFracTrans ,
  f z1 = w1 ∧
  f z2 = w2 ∧
  f z3 = w3 := by
    let fz := construct_lft_to0_1_infty z1 z2 z3 hz
    let gw := construct_lft_to0_1_infty w1 w2 w3 hw
    let compose_lft := comp (gw.inv) fz
    use compose_lft
    have ⟨hf1, hf2, hf3⟩ := constructlft_map_to_01infty z1 z2 z3 hz
    unfold compose_lft
    rw [comp_apply, comp_apply, comp_apply]
    have hfz_maps := constructlft_map_to_01infty z1 z2 z3 hz
    unfold fz
    rcases hfz_maps with ⟨hz1,hz2,hz3⟩
    rw [hz1,hz2,hz3]
    have hgz_maps := proof_inv_constructlft_map_to_01infty w1 w2 w3 hw
    rcases hgz_maps with ⟨hw1,hw2,hw3⟩
    unfold gw
    rw [hw1,hw2,hw3]
    trivial

end ThreePointsProperty




noncomputable section LFTProportionality

/--Define when two LFTs have proportional coefficients
-/
def LinearFracTrans.Proportional (f1 f2 : LinearFracTrans) : Prop :=
  ∃ (k : ℂ) , k ≠ 0 ∧
    f2.a = k * f1.a ∧
    f2.b = k * f1.b ∧
    f2.c = k * f1.c ∧
    f2.d = k * f1.d

/--Define when two LFTs give the same result for all inputs:
-/
def LinearFracTrans.FunEq (f1 f2 : LinearFracTrans) : Prop :=
  ∀ z : EComplex, f1 z = f2 z

/-- The main theorem: functional equality ↔ proportionality
Proportinal to FunEq -/
theorem proportional2FunEq (f1 f2 : LinearFracTrans) :
  f1.Proportional f2 → f1.FunEq f2 := by
    intro ⟨k, hk_ne, ha, hb, hc, hd⟩ z
    cases z with
    | none => {
      unfold LinearFracTrans.apply
      simp only
      split_ifs with h1c_eq0 h2c_neq0 h2c_eq0
      rfl
      push Not at h2c_neq0
      rw [h1c_eq0,mul_zero] at hc
      contradiction
      push Not at h1c_eq0
      rw [h2c_eq0] at hc
      rw[zero_eq_mul] at hc
      rcases hc with h1 | h2
      contradiction
      contradiction
      congr 1
      rw [ha,hc]
      field_simp
    }
    | some z => {
      unfold LinearFracTrans.apply
      simp only
      have f1_det : f1.a * f1.d - f1.b * f1.c ≠ 0 := by exact f1.determinant_ne_zero
      have f2_det : f2.a * f2.d - f2.b * f2.c ≠ 0 := by exact f2.determinant_ne_zero
      split_ifs with h1c_eq0 h2c_eq0 hcd hcdeq h2c_eq02 h1c_eq02 h2c_eq03 hcd2
      congr 1
      rw[ha,hb,hd]
      field_simp
      push Not at h2c_eq0
      rw [h1c_eq0,mul_zero] at hc
      contradiction
      congr 1
      push Not at hcd h2c_eq0
      field_simp
      rw [h1c_eq0,mul_zero] at hc
      rw [hc,mul_zero,zero_add]
      rw[h1c_eq0,mul_zero,sub_zero] at f1_det
      rw[hc,mul_zero,sub_zero] at f2_det
      have f1d_neq0 : f1.d ≠ 0 := by exact EComplex.coe_ne_coe_iff.mp fun a ↦ h2c_eq0 hc
      have f2d_neq0 : f2.d ≠ 0 := by exact EComplex.coe_ne_coe_iff.mp fun a ↦ h2c_eq0 hc
      field_simp
      rw [hb,ha,hd]
      ring
      push Not at h1c_eq0
      rw[h2c_eq02,zero_eq_mul] at hc
      rcases hc
      contradiction
      contradiction
      trivial
      push Not at h1c_eq0 h2c_eq02 h1c_eq02
      rw [hd,hc] at h1c_eq02
      field_simp at h1c_eq02
      rw[neg_div'] at h1c_eq02
      contradiction
      rw[h2c_eq03,zero_eq_mul] at hc
      push Not at h1c_eq0
      rcases hc
      contradiction
      contradiction
      push Not at hcdeq
      rw[hc,hd] at hcd2
      field_simp at hcd2 hcdeq
      push Not at h1c_eq0
      rw[neg_div'] at hcdeq
      rw[← propext (eq_div_iff_mul_eq h1c_eq0)] at hcd2
      contradiction
      congr 1
      push Not at h1c_eq0 hcdeq h2c_eq03 hcd2
      rw[ha,hb,hc,hd]
      field_simp
    }

/-If two LFTs agree everywhere, they agree on whether c = 0-/
lemma c_zero_iff_of_funEq
  (f1 f2 : LinearFracTrans) (h : f1.FunEq f2) :
  f1.c = 0 ↔ f2.c = 0 := by
  have h_inf := h none
  constructor
  · intro hc1
    simp [LinearFracTrans.apply, hc1] at h_inf
    exact h_inf
  · intro hc2
    simp [LinearFracTrans.apply,hc2] at h_inf
    exact h_inf


/--From FunEq at ∞ when both c ≠ 0 : a1/c1 = a2/c2 -/
lemma ratio_a_c_of_funEq_inf
  (f1 f2 : LinearFracTrans) (h : f1.FunEq f2)
  (hc1 : f1.c ≠ 0) (hc2 : f2.c ≠ 0) :
    f1.a / f1.c = f2.a / f2.c := by
  have h_inf := h none
  simp only [apply, hc1, ↓reduceIte, hc2] at h_inf
  exact (EComplex.some_eq_iff (f1.a / f1.c) (f2.a / f2.c)).mp h_inf

/-From FunEq at 0 : b1/d1 = b2/d2-/
lemma ratio_b_d_of_funEq_zero (f1 f2 : LinearFracTrans) (h : f1.FunEq f2)
    (hd1 : f1.d ≠ 0) (hd2 : f2.d ≠ 0) :
    f1.b / f1.d = f2.b / f2.d := by
  have h_zero := h (EComplex.some 0)
  simp [LinearFracTrans.apply] at h_zero
  by_cases hf1c : f1.c =0
  · have hf2c : f2.c = 0 := by exact (c_zero_iff_of_funEq f1 f2 h).mp hf1c
    simp only [hf1c, ↓reduceIte, hf2c, coe_eq_coe_iff] at h_zero
    exact h_zero
  · push Not at hf1c
    have hf2c : f2.c ≠ 0 := by
      intro hcon
      have hf1cc : f1.c = 0 := by exact (c_zero_iff_of_funEq f1 f2 h).mpr hcon
      contradiction
    simp only [hf1c, ↓reduceIte, hf2c] at h_zero
    have hcd1_neq0 : 0 ≠ -f1.d / f1.c := Ne.symm (div_ne_zero (neg_ne_zero.mpr hd1) hf1c)
    have hcd2_neq0 : 0 ≠ -f2.d / f2.c := Ne.symm (div_ne_zero (neg_ne_zero.mpr hd2) hf2c)
    simp [hcd1_neq0,hcd2_neq0] at h_zero
    exact h_zero

/- From FunEq at 1-/
lemma ratio_at_one_of_funEq (f1 f2 : LinearFracTrans) (h : f1.FunEq f2)
    (hd1 : f1.c + f1.d ≠ 0) (hd2 : f2.c + f2.d ≠ 0) :
    (f1.a + f1.b) / (f1.c + f1.d) = (f2.a + f2.b) / (f2.c + f2.d) := by
  have h_one := h (EComplex.some 1)
  simp [LinearFracTrans.apply] at h_one
  by_cases hf1c : f1.c = 0
  · have hf2c : f2.c = 0 := by exact (c_zero_iff_of_funEq f1 f2 h).mp hf1c
    simp only [hf1c, ↓reduceIte, hf2c, coe_eq_coe_iff] at h_one
    rw [hf1c,hf2c,zero_add,zero_add]
    rw [add_div, add_div]
    exact h_one
  · push Not at hf1c
    have hf2c : f2.c ≠ 0 := by
      intro hcc
      have hf1cc : f1.c = 0 := by exact (c_zero_iff_of_funEq f1 f2 h).mpr hcc
      contradiction
    simp only [hf1c, ↓reduceIte, hf2c] at h_one
    have h1 : 1 ≠ -f1.d / f1.c := fun heq => hd1 (by field_simp [hf1c] at heq; rw [heq]; ring)
    have h2 : 1 ≠ -f2.d / f2.c := fun heq => hd2 (by field_simp [hf2c] at heq; rw [heq]; ring)
    simp only [if_neg h1, if_neg h2] at h_one
    have h11 := Option.some_injective ℂ h_one
    exact h11

/-- If two LFTs are FunEq and both have c ≠ 0, they have the same pole -/
lemma pole_eq_of_funEq (f1 f2 : LinearFracTrans) (h : f1.FunEq f2)
    (hc1 : f1.c ≠ 0) (hc2 : f2.c ≠ 0) :
    pole f1 = pole f2 := by
  have h_pole := h (EComplex.some (-f1.d/f1.c))
  simp only [apply] at h_pole
  have f1_pole : f1.c * (-f1.d / f1.c) + f1.d = 0 := by {
    field_simp
    ring
  }
  simp [hc1,hc2] at h_pole
  unfold pole
  exact
    (EComplex.some_eq_iff (-f1.d / f1.c) (-f2.d / f2.c)).mp
      (congrArg EComplex.Complex.toEComplex h_pole)

/-From equal poles,derive d2 = k * d1 where k = c2/c1-/
lemma pro_d_of_pole_eq (f1 f2 : LinearFracTrans)
    (hc1 : f1.c ≠ 0) (hc2 : f2.c ≠ 0)
    (h_pole : f1.pole = f2.pole) :
    f2.d = (f2.c / f1.c) * f1.d := by
  simp only [pole] at h_pole
  have h : f1.d / f1.c = f2.d / f2.c := by
    field_simp at h_pole
    field_simp
    simp at h_pole
    exact h_pole
  field_simp at h
  field_simp
  rw [Eq.comm,mul_comm,mul_comm f2.d f1.c]
  exact h


/-! ## Lemmas for pole that require c ≠ 0 (full Möbius case) -/

/-- f(∞) = a/c when c ≠ 0 -/
lemma apply_none (f : LinearFracTrans) (hc : f.c ≠ 0) :
    f none = EComplex.some (f.a / f.c) := by
  simp only [apply, hc, ↓reduceIte]

/-- f(w) for finite w not at pole (requires c ≠ 0) -/
lemma apply_some_of_ne_pole (f : LinearFracTrans) (hc : f.c ≠ 0)
    (w : ℂ) (hw : f.c * w + f.d ≠ 0) :
    f (EComplex.some w) = EComplex.some ((f.a * w + f.b) / (f.c * w + f.d)) := by
  simp only [apply, hc, ↓reduceIte]
  by_cases h : w = -f.d / f.c
  · exfalso
    apply hw
    rw [h]
    field_simp [hc]
    simp only [neg_add_cancel, mul_zero]
  · simp only [h, ↓reduceIte]

/-- f(w) = ∞ when w is at the pole (requires c ≠ 0) -/
lemma apply_some_of_pole (f : LinearFracTrans) (hc : f.c ≠ 0)
    (w : ℂ) (hw : f.c * w + f.d = 0) :
    f (EComplex.some w) = none := by
  simp only [apply, hc, ↓reduceIte]
  have : w = -f.d / f.c := by
    field_simp [hc] at hw
    field_simp [hc]
    rw [eq_neg_iff_add_eq_zero,mul_comm]
    exact hw
  simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not]
  exact this

/-- w is at pole iff w = -d/c (requires c ≠ 0) -/
lemma pole_iff (f : LinearFracTrans) (hc : f.c ≠ 0) (w : ℂ) :
    f.c * w + f.d = 0 ↔ w = -f.d / f.c := by
  constructor
  · intro h
    field_simp [hc] at h
    field_simp [hc]
    rw [eq_neg_iff_add_eq_zero,mul_comm]
    exact h
  · intro h
    simp [h]
    field_simp [hc]
    simp only [neg_add_cancel, mul_zero]


/-- Difference of two finite images (requires c ≠ 0 for the denominator form) -/
lemma apply_sub_apply (f : LinearFracTrans)
    (w1 w2 : ℂ) (hw1 : f.c * w1 + f.d ≠ 0) (hw2 : f.c * w2 + f.d ≠ 0) :
    (f.a * w1 + f.b) / (f.c * w1 + f.d) - (f.a * w2 + f.b) / (f.c * w2 + f.d) =
    (f.a * f.d - f.b * f.c) * (w1 - w2) / ((f.c * w1 + f.d) * (f.c * w2 + f.d)) := by
  rw [div_sub_div _ _ hw1 hw2]
  congr 1
  ring

/-- a/c - f(w) (requires c ≠ 0) -/
lemma apply_none_sub_apply (f : LinearFracTrans) (hc : f.c ≠ 0)
    (w : ℂ) (hw : f.c * w + f.d ≠ 0) :
    f.a / f.c - (f.a * w + f.b) / (f.c * w + f.d) =
    (f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
  field_simp [hc, hw]
  ring

/-- f(w) - a/c (requires c ≠ 0) -/
lemma apply_sub_apply_none (f : LinearFracTrans) (hc : f.c ≠ 0)
    (w : ℂ) (hw : f.c * w + f.d ≠ 0) :
    (f.a * w + f.b) / (f.c * w + f.d) - f.a / f.c =
    -(f.a * f.d - f.b * f.c) / (f.c * (f.c * w + f.d)) := by
  field_simp [hc, hw]
  rw [mul_comm] at hw
  field_simp [hw]
  ring_nf

/-- If w1 ≠ w2 and w1 is at pole, then w2 is not at pole (requires c ≠ 0) -/
lemma LinearFracTrans.ne_pole_of_ne_of_pole (f : LinearFracTrans) (hc : f.c ≠ 0)
    (w1 w2 : ℂ) (hne : w1 ≠ w2) (hw1 : f.c * w1 + f.d = 0) :
    f.c * w2 + f.d ≠ 0 := by
  intro h
  have eq2 : w2 = -f.d / f.c := by
    field_simp [hc] at h
    field_simp [hc]
    rw [eq_neg_iff_add_eq_zero,mul_comm]
    exact h
  have eq1 : w1 = -f.d / f.c := by
    field_simp [hc] at hw1
    field_simp [hc]
    rw [eq_neg_iff_add_eq_zero,mul_comm]
    exact hw1
  exact hne (by rw [eq1, eq2])


/-! ## Lemmas for c = 0 (affine case) -/

/-- When c = 0, d ≠ 0 (from determinant) -/
lemma d_ne_zero_of_c_zero (f : LinearFracTrans) (hc : f.c = 0) : f.d ≠ 0 := by
  intro hd
  have := f.determinant_ne_zero
  simp only [hc, hd, mul_zero, sub_zero] at this
  contradiction

/-- When c = 0, a ≠ 0 (from determinant) -/
lemma a_ne_zero_of_c_zero (f : LinearFracTrans) (hc : f.c = 0) : f.a ≠ 0 := by
  intro ha
  have := f.determinant_ne_zero
  simp only [hc, ha, zero_mul, mul_zero, zero_sub] at this
  rw[neg_ne_zero] at this
  contradiction

/-- f(∞) = ∞ when c = 0 -/
lemma apply_none_of_c_zero (f : LinearFracTrans) (hc : f.c = 0) :
    f none = none := by
  simp only [apply, hc, ↓reduceIte]

/-- f(w) = (a/d)w + (b/d) when c = 0 -/
lemma apply_some_of_c_zero (f : LinearFracTrans) (hc : f.c = 0) (w : ℂ) :
    f (EComplex.some w) = EComplex.some ((f.a / f.d) * w + (f.b / f.d)) := by
  simp only [apply, hc, ↓reduceIte]

/-- Difference of affine images when c = 0 -/
lemma apply_sub_of_c_zero (f : LinearFracTrans) (w1 w2 : ℂ) :
    (f.a / f.d) * w1 + (f.b / f.d) - ((f.a / f.d) * w2 + (f.b / f.d)) =
    (f.a / f.d) * (w1 - w2) := by
  ring


/--Main case when both c ≠ 0-/
lemma proportional_of_c_ne_zero (f1 f2 : LinearFracTrans) (h : f1.FunEq f2)
    (hc1 : f1.c ≠ 0) (hc2 : f2.c ≠ 0) : f1.Proportional f2 := by
  use f2.c / f1.c
  let k := f2.c / f1.c
  have h1 : f2.c / f1.c ≠ 0 := by exact div_ne_zero hc2 hc1
  constructor
  exact h1
  have pro_a : f2.a = k * f1.a := by {
    have h_ac := ratio_a_c_of_funEq_inf f1 f2 h hc1 hc2
    unfold k
    field_simp at h_ac ⊢
    exact
      (EComplex.some_eq_iff (f1.c * f2.a) (f1.a * f2.c)).mp
        (congrArg EComplex.Complex.toEComplex (_root_.id (Eq.symm h_ac)))
  }
  have pro_c : f2.c = k * f1.c := by {
    unfold k
    field_simp
  }
  have pro_d : f2.d = k * f1.d := by {
    have h_same_pole := pole_eq_of_funEq f1 f2 h hc1 hc2
    exact pro_d_of_pole_eq f1 f2 hc1 hc2 h_same_pole
  }
  have pro_b : f2.b = k * f1.b := by {
    by_cases hd1 : f1.d = 0
    --cases d1 = 0
    · {
      have hd2 : f2.d =0 := by simp [pro_d,hd1]
      have h_one := h (EComplex.some 1)
      simp only [apply] at h_one
      have hcd1 : 1 ≠  -f1.d / f1.c := by simp [hd1]
      have hcd2 : 1 ≠  -f2.d / f2.c := by simp [hd2]
      simp only [hc1, ↓reduceIte, hcd1, mul_one, hc2, hcd2] at h_one
      have h_eq := Option.some_injective ℂ h_one
      simp only [hd1, add_zero, hd2] at h_eq
      have h_cross : (f1.a + f1.b) * f2.c = (f2.a + f2.b) * f1.c := by
        field_simp [hc1,hc2] at h_eq
        rw[mul_comm (f2.a + f2.b) f1.c]
        exact h_eq
      field_simp [hc1] at h_cross ⊢
      rw [pro_a,pro_c] at h_cross
      unfold k at h_cross
      field_simp at h_cross
      rw [add_mul,add_left_cancel_iff] at h_cross
      unfold k
      field_simp
      rw[Eq.comm,mul_comm f2.b _]
      exact h_cross
      }
    --cases d1 ≠ 0
    · {
      push Not at hd1
      have hk : f2.c / f1.c ≠ 0 := div_ne_zero hc2 hc1
      have hd2 : f2.d ≠ 0 := by
        rw [pro_d]
        exact mul_ne_zero hk hd1
      have h_zero := h (EComplex.some 0)
      simp only [apply] at h_zero
      have hz1 : 0 ≠  -f1.d / f1.c := by {
        by_contra h
        field_simp at h
        rw[zero_mul,eq_neg_iff_add_eq_zero,zero_add] at h
        contradiction
      }
      have hz2 : 0 ≠  -f2.d / f2.c := by {
        by_contra h
        field_simp at h
        rw[zero_mul,eq_neg_iff_add_eq_zero,zero_add] at h
        contradiction
      }
      simp [hc1,hc2,hz1,hz2] at h_zero
      have h_cross : f1.b * f2.d = f2.b * f1.d := by
        field_simp [hd1, hd2] at h_zero
        rw[mul_comm f1.d _] at h_zero
        exact h_zero
      rw [pro_d] at h_cross
      field_simp [hd1] at h_cross ⊢
      rw[Eq.comm]
      exact h_cross
      }
  }
  unfold k at pro_a pro_b pro_c pro_d
  constructor
  exact pro_a
  constructor
  exact pro_b
  constructor
  exact pro_c
  exact pro_d


/-Main case when both c = 0-/
lemma proportional_of_c_zero (f1 f2 : LinearFracTrans) (h : f1.FunEq f2)
    (hc1 : f1.c = 0) (hc2 : f2.c = 0) : f1.Proportional f2 := by
  have hd1 : f1.d ≠ 0 := by
    intro hd
    have := f1.determinant_ne_zero
    simp [hc1,hd] at this
  have hd2 : f2.d ≠ 0 := by
    intro hd
    have := f2.determinant_ne_zero
    simp [hc2,hd] at this
  let k := f2.d / f1.d
  have hk : k ≠ 0 := div_ne_zero hd2 hd1
  use k
  have pro_a : f2.a = k * f1.a := by {
    have h_zero := h (EComplex.some 0)
    simp only [apply, hc1, hc2] at h_zero
    simp at h_zero
    have h_bd : f1.b / f1.d = f2.b / f2.d :=
      by exact h_zero
    have h_one := h (EComplex.some 1)
    simp only [apply, hc1, hc2] at h_one
    simp at h_one
    have h_sum : (f1.a + f1.b) / f1.d = (f2.a + f2.b) / f2.d := by
      rw [add_div, add_div]
      exact h_one
    have h_ad : f1.a / f1.d = f2.a / f2.d := by {
      have h1 : (f1.a + f1.b) / f1.d - f1.b / f1.d = (f2.a + f2.b) / f2.d - f2.b / f2.d := by
        rw [h_sum, h_bd]
      simp only [add_div, add_sub_cancel_right] at h1
      exact h1
    }
    field_simp [hd1]
    have h_cross : f1.a * f2.d = f2.a * f1.d := by
      field_simp [hd1, hd2] at h_ad
      rw[mul_comm f1.d _] at h_ad
      exact h_ad
    unfold k
    field_simp
    rw[Eq.comm,mul_comm f2.d _ ]
    exact h_cross
  }
  have pro_b : f2.b = k * f1.b := by {
    have h_zero := h (EComplex.some 0)
    simp only [apply, hc1, hc2] at h_zero
    simp at h_zero
    have h_bd := by exact h_zero
    have h_bd_cross : f1.b * f2.d = f2.b * f1.d := by
      field_simp [hd1, hd2] at h_bd
      rw [mul_comm f2.b _]
      exact h_bd
    field_simp [hd1]
    unfold k
    field_simp
    rw[Eq.comm,mul_comm f2.d _]
    exact h_bd_cross
  }
  have pro_c : f2.c = k * f1.c := by {
    simp [hc1,hc2]
  }
  have pro_d : f2.d = k * f1.d := by {
    simp only [k]
    field_simp
  }
  constructor
  exact hk
  constructor
  exact pro_a
  constructor
  exact pro_b
  constructor
  exact pro_c
  exact pro_d


/-- FunEq to Proportional-/
theorem FunEq2proportional
  (f1 f2 : LinearFracTrans) (h : f1.FunEq f2) :
    f1.Proportional f2 := by
  have hc_equiv : f1.c = 0 ↔ f2.c = 0 := c_zero_iff_of_funEq f1 f2 h
  by_cases hc1 : f1.c = 0
  · have hc2 : f2.c = 0 := hc_equiv.mp hc1
    exact proportional_of_c_zero f1 f2 h hc1 hc2
  · have hc2 : f2.c ≠ 0 := fun h2 => hc1 (hc_equiv.mpr h2)
    exact proportional_of_c_ne_zero f1 f2 h hc1 hc2

/--  #### Remark after Theorem 2.3.7
  Two LFTs are functionally equal iff their coefficients
  are proportional -/
theorem funEq_iff_proportional (f1 f2 : LinearFracTrans) :
    f1.FunEq f2 ↔ f1.Proportional f2 := by
  constructor
  · exact fun a ↦ FunEq2proportional f1 f2 a
  · exact fun a ↦ proportional2FunEq f1 f2 a

/-
  We define an equivalence relation on
  `LinearFractionalTransformation` by proportionality:
  two transformations are equivalent if one is a nonzero
  scalar multiple of the other.
-/

/-- `lftEquiv f g` is the proposition that `f` and `g`
    are proportional. -/
def lftEquiv (f g : LinearFracTrans) : Prop
  := Proportional f g

/-- Proportionality is reflexive:
  every transformation is proportional to itself
  (via the scalar `1`). -/
theorem lftproportional_refl
  (f : LinearFracTrans) : lftEquiv f f := by
  -- Expand the equivalence and the underlying
  -- `proportional` predicate.
  unfold lftEquiv
  unfold Proportional
  -- Provide the scalar `1`.
  use 1
  constructor
  · -- `1 ≠ 0` in the complex numbers.
    exact Ne.symm (zero_ne_one' ℂ)
  · -- The four components are preserved because
    -- multiplying by `1` changes nothing.
    refine ⟨?h1, ?h2, ?h3, ?h4⟩
    rw [one_mul]
    rw [one_mul]
    rw [one_mul]
    rw [one_mul]

/-- Proportionality is symmetric: if `f` is
  proportional to `g` with nonzero scalar `k`,
  then `g` is proportional to `f` with scalar `1/k`.
-/
theorem lftproportional_symm {f g : LinearFracTrans} :
    lftEquiv f g → lftEquiv g f := by
  unfold lftEquiv
  intro h
  unfold Proportional at h
  unfold Proportional
  -- Extract the scalar `k` and the component
  -- equations from `h`.
  rcases h with ⟨k, hk, ha, hb, hc, hd⟩
  -- The inverse scalar is `1/k`.
  let k1 := 1 / k
  -- Since `k ≠ 0`, the inverse is also nonzero.
  have k1_neq0 : k1 ≠ 0 := by
    exact one_div_ne_zero hk
  use k1
  constructor
  · exact k1_neq0
  · unfold k1
    -- Rewrite each component equation and use
    -- field algebra to simplify.
    refine ⟨?h1, ?h2, ?h3, ?h4⟩
    · rw [ha]
      field_simp
    · rw [hb]
      field_simp
    · rw [hc]
      field_simp
    · rw [hd]
      field_simp

/-- Proportionality is transitive: if `f` is proportional
  to `g` (scalar `k₁`) and `g` to `h` (scalar `k₂`),
  then `f` is proportional to `h` (scalar `k₁*k₂`). -/
theorem lftproportional_trans {f g h : LinearFracTrans} :
    lftEquiv f g → lftEquiv g h → lftEquiv f h := by
  unfold lftEquiv
  intro hfg hgh
  unfold Proportional at hfg hgh
  -- Extract the scalars and the component equalities
  -- from both hypotheses.
  rcases hfg with ⟨k1, hk1, haf, hbf, hcf, hdf⟩
  rcases hgh with ⟨k2, hk2, hag, hbg, hcg, hdg⟩
  unfold Proportional
  -- The product `k1*k2` is nonzero because both factors
  --  are nonzero.
  use k1 * k2
  refine ⟨?hneq0, ?h1, ?h2, ?h3, ?h4⟩
  · -- `mul_ne_zero_iff_right` reduces to showing `k1 ≠ 0`,
    -- which we have.
    exact (mul_ne_zero_iff_right hk2).mpr hk1
  · -- `f.a = (k1*k2)*h.a` follows by associativity and
    --  the two given equations.
    rw [mul_assoc,hag,haf]
    ring
  · rw [mul_assoc, hbg, hbf]
    ring
  · rw [mul_assoc, hcg, hcf]
    ring
  · rw [mul_assoc, hdg, hdf]
    ring


/-- The setoid instance that makes
  `LinearFractionalTransformation` into a type
  with an equivalence relation given by proportionality.
-/
def lftsetoid : Setoid LinearFracTrans := {
  r := lftEquiv
  iseqv := {
    refl := lftproportional_refl
    symm := lftproportional_symm
    trans := lftproportional_trans
  }
}

/- The quotient type of `LinearFractionalTransformation`
   by proportionality. This represents the set of
   proportionality classes, which will later be equipped
   with a group structure (the quotient group).
-/


/-- Multiplication respects proportionality:
  if f' = k₁·f and g' = k₂·g,
   then f' * g' = (k₁·k₂)·(f*g).
-/
theorem proportional_mul {f f' g g' : LinearFracTrans}
    (hf : Proportional f f') (hg : Proportional g g')
  : Proportional (f * g) (f' * g') := by
  rcases hf with ⟨k₁, hk₁, haf, hbf, hcf, hdf⟩
  rcases hg with ⟨k₂, hk₂, hag, hbg, hcg, hdg⟩
  use k₁ * k₂
  constructor
  · exact mul_ne_zero hk₁ hk₂
  · -- Now we need four component equations: (f'*g').a = (k₁*k₂) * (f*g).a, etc.
    -- Recall: mul = comp, defined by matrix multiplication.
    -- We prove each with a `calc` block that expands `comp` and rewrites using haf,...
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        (f' * g').a = f'.a * g'.a + f'.b * g'.c := rfl
        _ = (k₁ * f.a) * (k₂ * g.a) + (k₁ * f.b) * (k₂ * g.c) := by rw [haf, hag, hbf, hcg]
        _ = (k₁ * k₂) * (f.a * g.a + f.b * g.c) := by ring
        _ = (k₁ * k₂) * (f * g).a := rfl
    · calc
        (f' * g').b = f'.a * g'.b + f'.b * g'.d := rfl
        _ = (k₁ * f.a) * (k₂ * g.b) + (k₁ * f.b) * (k₂ * g.d) := by rw [haf, hbg, hbf, hdg]
        _ = (k₁ * k₂) * (f.a * g.b + f.b * g.d) := by ring
        _ = (k₁ * k₂) * (f * g).b := rfl
    · calc
        (f' * g').c = f'.c * g'.a + f'.d * g'.c := rfl
        _ = (k₁ * f.c) * (k₂ * g.a) + (k₁ * f.d) * (k₂ * g.c) := by rw [hcf, hag, hdf, hcg]
        _ = (k₁ * k₂) * (f.c * g.a + f.d * g.c) := by ring
        _ = (k₁ * k₂) * (f * g).c := rfl
    · calc
        (f' * g').d = f'.c * g'.b + f'.d * g'.d := rfl
        _ = (k₁ * f.c) * (k₂ * g.b) + (k₁ * f.d) * (k₂ * g.d) := by rw [hcf, hbg, hdf, hdg]
        _ = (k₁ * k₂) * (f.c * g.b + f.d * g.d) := by ring
        _ = (k₁ * k₂) * (f * g).d := rfl



/-- Inverse respects proportionality:
  if f' = k·f, then (f')⁻¹ = (1/k)·f⁻¹. -/
theorem proportional_inv {f f' : LinearFracTrans}
  (hf : Proportional f f') :
    Proportional (f⁻¹) (f'⁻¹) := by
  rcases hf with ⟨k, hk, ha, hb, hc, hd⟩
  use 1 / k
  constructor
  · exact one_div_ne_zero hk
  · -- Need four component equations.
    -- Let D := det f = f.a*f.d - f.b*f.c.
    -- For f', det f' = (k*f.a)*(k*f.d) - (k*f.b)*(k*f.c) = k^2 * D.
    -- Then (f'⁻¹).a = f'.d / det(f') = (k*f.d) / (k^2 * D) = (1/k)*(f.d/D) = (1/k)*(f⁻¹).a.
    -- We'll unfold inv, introduce D, and field_simp [hk, D].
    -- But we must be careful: D ≠ 0 because LinearFracTrans requires det ≠ 0.
    -- Let D := f.a * f.d - f.b * f.c, and similarly D' for f'.
    -- We'll use the property f.determinant_ne_zero.
    -- Here is a direct calc:
    set D := f.a * f.d - f.b * f.c with hD
    have hD_ne_zero : D ≠ 0 := f.determinant_ne_zero
    have hD' : f'.a * f'.d - f'.b * f'.c = k^2 * D := by
      rw [ha, hb, hc, hd]
      ring
    have denomi_neq0 : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
    -- Now expand inv
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (f'⁻¹).a = (1/k) * (f⁻¹).a
      dsimp [Inv.inv, LinearFracTrans.inv]
      -- This gives (f'.d / (f'.a * f'.d - f'.b * f'.c)) = (1/k) * (f.d / D)
      rw [hD']
      rw [hd]
      -- hd: f'.d = k * f.d
      -- goal: (k * f.d) / (k^2 * D) = (1/k) * (f.d / D)
      rw [mul_comm f.a _] at denomi_neq0
      field_simp [hD_ne_zero, hk,denomi_neq0]
      ring
    · -- b component
      dsimp [Inv.inv, LinearFracTrans.inv]
      rw [hD']
      rw [hb]  -- hb: f'.b = k * f.b
      have denomi_neq0 : f.a * f.d - f.b * f.c ≠ 0 := f.determinant_ne_zero
      field_simp [hD_ne_zero, hk,denomi_neq0]
      rw [hD]
    · -- c component
      dsimp [Inv.inv, LinearFracTrans.inv]
      rw [hD']
      rw [hc]  -- hc: f'.c = k * f.c
      field_simp [hD_ne_zero, hk,denomi_neq0]
      rw [mul_comm f.b _] at denomi_neq0
      field_simp
      ring
    · -- d component
      dsimp [Inv.inv, LinearFracTrans.inv]
      rw [hD']
      rw [ha]  -- ha: f'.a = k * f.a
      field_simp [hD_ne_zero, hk]
      ring



-- Now lift the operations to the quotient
@[simp]
def quotMul : Quotient lftsetoid → Quotient lftsetoid → Quotient lftsetoid :=
  Quotient.lift₂ (fun f g : LinearFracTrans => ⟦f * g⟧) (by
    intro f g f' g' hf hg
    apply Quotient.sound
    exact proportional_mul hf hg)
@[simp]
def quotInv : Quotient lftsetoid → Quotient lftsetoid :=
  Quotient.lift (fun f : LinearFracTrans => ⟦f⁻¹⟧) (by
    intro f f' hf
    apply Quotient.sound
    exact proportional_inv hf)

@[simp]
def quotOne : Quotient lftsetoid := ⟦(1 : LinearFracTrans)⟧

instance : Mul (Quotient lftsetoid) := ⟨quotMul⟩
instance : Inv (Quotient lftsetoid) := ⟨quotInv⟩
instance : One (Quotient lftsetoid) := ⟨quotOne⟩

/-- The product of two quotient classes `⟦f⟧ * ⟦g⟧` equals the class of the product `⟦f * g⟧`. -/
lemma mul_mk (f g : LinearFracTrans) : (⟦f⟧ : Quotient lftsetoid) * ⟦g⟧ = ⟦f * g⟧ := rfl

/-- The identity element of the quotient group is the class of the identity `⟦1⟧`. -/
lemma one_mk : (1 : Quotient lftsetoid) = ⟦(1 : LinearFracTrans)⟧ := rfl

/-- The inverse of a quotient class `⟦f⟧⁻¹` equals the class of the inverse `⟦f⁻¹⟧`. -/
lemma inv_mk (f : LinearFracTrans) : (⟦f⟧ : Quotient lftsetoid)⁻¹ = ⟦f⁻¹⟧ := rfl


#check ⟦(1 : LinearFracTrans)⟧ * ⟦(1 : LinearFracTrans)⟧



/-- The quotient group of `LinearFracTrans` by the
  proportionality equivalence relation. Two transformations
  are identified if they are nonzero scalar multiples of
  each other. This group is isomorphic to the projective
  general linear group `PGL(2, ℂ)`.
-/
instance : Group (Quotient lftsetoid) := by
  refine
    { one := quotOne
      mul := quotMul
      inv := quotInv
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      inv_mul_cancel := ?_
    }
  · -- mul_assoc : (x * y) * z = x * (y * z)
    intro x y z
    -- Replace x, y, z with representatives f, g, h
    refine Quotient.ind (motive := fun x' : Quotient lftsetoid => (x' * y) * z = x' * (y * z)) ?_ x
    intro f
    refine Quotient.ind (motive := fun y' : Quotient lftsetoid => (⟦f⟧ * y') * z = ⟦f⟧ * (y' * z)) ?_ y
    intro g
    refine Quotient.ind (motive := fun z' : Quotient lftsetoid => (⟦f⟧ * ⟦g⟧) * z' = ⟦f⟧ * (⟦g⟧ * z')) ?_ z
    intro h
    -- Goal: (⟦f⟧ * ⟦g⟧) * ⟦h⟧ = ⟦f⟧ * (⟦g⟧ * ⟦h⟧)
    -- Expand all multiplications using mul_mk
    rw [mul_mk f g, mul_mk (f * g) h, mul_mk g h, mul_mk f (g * h)]
    -- Goal: ⟦(f * g) * h⟧ = ⟦f * (g * h)⟧
    -- Use associativity in the underlying group
    rw [mul_assoc f g h]
  · -- left identity
    -- Replace x by a representative f
    refine Quotient.ind (motive := fun x' : Quotient lftsetoid => (1 : Quotient lftsetoid) * x' = x') ?_
    intro f
    -- Goal: 1 * ⟦f⟧ = ⟦f⟧
    -- Expand the unit 1 into ⟦1⟧ using one_mk
    rw [one_mk]
    -- Goal: ⟦1⟧ * ⟦f⟧ = ⟦f⟧
    -- Expand the multiplication using mul_mk
    rw [mul_mk]
    -- Goal: ⟦1 * f⟧ = ⟦f⟧
    -- Use left identity in the underlying group
    rw [one_mul f]
  · -- right identity
    -- Replace x by a representative f
    refine Quotient.ind (motive := fun x' : Quotient lftsetoid => x' * (1 : Quotient lftsetoid) = x') ?_
    intro f
    -- Goal: ⟦f⟧ * 1 = ⟦f⟧
    -- Expand the right-hand side unit 1 into ⟦1⟧ using one_mk
    rw [one_mk]
    -- Goal: ⟦f⟧ * ⟦1⟧ = ⟦f⟧
    -- Expand the multiplication using mul_mk
    rw [mul_mk]
    -- Goal: ⟦f * 1⟧ = ⟦f⟧
    -- Use right identity in the underlying group
    rw [mul_one f]
  · -- left inverse
    -- Replace the quotient element x by a representative f
    refine Quotient.ind (motive := fun x' : Quotient lftsetoid => x'⁻¹ * x' = (1 : Quotient lftsetoid)) ?_
    intro f
    -- Goal: (⟦f⟧)⁻¹ * ⟦f⟧ = 1
    -- Expand the inverse using inv_mk
    rw [inv_mk f]
    -- Goal: ⟦f⁻¹⟧ * ⟦f⟧ = 1
    -- Expand the multiplication using mul_mk
    rw [mul_mk]
    -- Goal: ⟦f⁻¹ * f⟧ = 1
    -- Expand the right-hand side unit using one_mk
    rw [one_mk]
    -- Goal: ⟦f⁻¹ * f⟧ = ⟦1⟧
    -- Use the underlying group axiom inv_mul_cancel (or simply rewrite f⁻¹ * f = 1)
    rw [inv_mul_cancel f]
    -- Goal: ⟦1⟧ = ⟦1⟧, automatically true


end LFTProportionality






section LFT_fixed_point_property

/-
## Fixed point property of linear fractional transformation
-/

/-- Infinity is fixed by T iff c = 0
 see `IsAffine_iff_infty` in Chapter 2_3
-/
lemma infty_fixed_iff (T : LinearFracTrans) :
    T none = none ↔ T.c = 0 := by
  simpa only [infty, IsAffine]
    using (IsAffine_iff_infty T).symm

/-- Finite fixed points of an LFT
    satisfy a quadratic equation c z^2 + (d - a)*z - b = 0
-/
lemma finite_fixed_iff
  (T : LinearFracTrans) (z : ℂ) (hdenom : T.c * z + T.d ≠ 0) :
    T (EComplex.some z) = EComplex.some z
    ↔ T.c * z ^2 + (T.d -T.a) * z - T.b = 0
    := by
  simp only [apply]
  split_ifs with h hneg
  · {
    constructor
    intro hsome
    injection hsome with hsome
    rw [h,zero_mul,zero_add,sub_mul]
    field_simp at hsome
    have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
    rw [h,mul_zero,sub_zero,mul_ne_zero_iff] at det_not_zero
    rcases det_not_zero with ⟨ha,hd⟩
    field_simp at hsome
    rw[sub_eq_zero,sub_eq_iff_eq_add',mul_comm,Eq.comm]
    exact hsome
    intro hzero
    rw [h,zero_mul,zero_add,sub_mul] at hzero
    congr 1
    have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
    rw [h,mul_zero,sub_zero,mul_ne_zero_iff] at det_not_zero
    rcases det_not_zero with ⟨ha,hd⟩
    field_simp
    rw [sub_eq_zero,sub_eq_iff_eq_add',Eq.comm] at hzero
    exact hzero
    }
  · {
    push Not at h
    constructor
    simp
    intro hzero
    field_simp at hneg
    rw [← propext (eq_div_iff_mul_eq h)] at hneg
    rw [hneg] at hzero
    field_simp at hzero
    ring_nf at hzero
    have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
    rw [mul_comm,mul_comm T.b _] at det_not_zero
    exact Ne.elim det_not_zero hzero
    }
  · {
    push Not at h hneg
    constructor
    intro hsome
    injection hsome with hsome
    rw [mul_comm] at hdenom
    field_simp at hsome
    rw[mul_add] at hsome
    rw [sub_mul,add_sub,sub_eq_iff_eq_add',add_zero,sub_eq_iff_eq_add',hsome]
    ring_nf
    intro hsome
    congr 1
    rw [sub_eq_zero,Eq.comm] at hsome
    apply (div_eq_iff hdenom).2
    rw [hsome]
    ring_nf
    }

/-- Coefficient conditions imply functional identity
-/
lemma coeff_id_implies_fun_id (T : LinearFracTrans)
    (hc : T.c = 0) (ha : T.a = T.d) (hb : T.b = 0) :
    FunEq T id := by
  -- verify that T is proportional to the identity LFT
  have proportional_T_id : T.Proportional id := by
    unfold Proportional
    have det_not_zero : T.a * T.d - T.b * T.c ≠ 0
      := by exact T.determinant_ne_zero
    rw [hb,zero_mul,sub_zero,mul_ne_zero_iff]
      at det_not_zero
    rcases det_not_zero with ⟨ha_neg,hd_neg⟩
    use 1/T.a
    constructor
    exact one_div_ne_zero ha_neg
    constructor
    rw [one_div_mul_cancel ha_neg]
    rfl
    constructor
    rw [hb,mul_zero]
    rfl
    constructor
    rw[hc,mul_zero]
    rfl
    rw [ha,one_div_mul_cancel]
    rfl
    exact hd_neg
  -- If T is proportional to id, then they induce
  -- the same function on EComplex
  exact proportional2FunEq T id proportional_T_id

/-- Key algebraic fact:
 a quadratic cz² + ez + f = 0 with c ≠ 0
 has at most 2 solutions
-/
lemma quadratic_at_most_two_roots (c e f : ℂ) (hc : c ≠ 0)
    (z1 z2 z3 : ℂ) (hdist : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z1 ≠ z3)
    (h1 : c * z1 ^ 2 + e * z1 + f = 0)
    (h2 : c * z2 ^ 2 + e * z2 + f = 0)
    (h3 : c * z3 ^ 2 + e * z3 + f = 0) :
    False := by
  have key12 : c * (z1 + z2) + e = 0 := by
    have hsub : c * z1 ^ 2 + e * z1 + f - (c * z2 ^ 2 + e * z2 + f) = 0 := by
      rw [h1,h2]; ring
    have hfactor : (z1 - z2) * (c * (z1 + z2) + e) = 0 := by
      calc (z1 - z2) * (c * (z1 + z2) + e)
          = c * z1^2 - c * z2^2 + e * z1 - e * z2 := by ring
        _ = c * z1^2 + e * z1 + f - (c * z2^2 + e * z2 + f) := by ring
        _ = 0 := hsub
    have hz12 : z1 - z2 ≠ 0 := sub_ne_zero.mpr hdist.1
    exact (mul_eq_zero_iff_left hz12).mp hfactor
  have key13 : c * (z1 + z3) + e = 0 := by
    have hsub : c * z1^2 + e * z1 + f - (c * z3^2 + e * z3 + f) = 0 := by
      rw [h1,h3]; ring
    have hfactor : (z1 - z3) * (c * (z1 + z3) + e) = 0 := by
      calc (z1 - z3) * (c * (z1 + z3) + e)
          = c * z1^2 - c * z3^2 + e * z1 - e * z3 := by ring
        _ = c * z1^2 + e * z1 + f - (c * z3^2 + e * z3 + f) := by ring
        _ = 0 := hsub
    have hz13 : z1 - z3 ≠ 0 := sub_ne_zero.mpr hdist.2.2
    exact (mul_eq_zero_iff_left hz13).mp hfactor
  have heq : c * (z1 + z2) = c * (z1 + z3) := by
    calc c * (z1 + z2) = -e := by exact Eq.symm (neg_eq_of_add_eq_zero_left key12)
    _ = c * (z1 + z3) := by exact neg_eq_of_add_eq_zero_left key13
  have this1 : z1 + z2 = z1 + z3 := by
    have := mul_left_cancel₀ hc heq
    exact this
  have this2 : z2 = z3 := add_left_cancel this1
  exact hdist.2.1 this2

/--
 When c = 0: the "quadratic" (d-a)z - b = 0 is linear
 If d ≠ a, it has exactly one root
 If d = a and b ≠ 0, it has no roots
 If d = a and b = 0, every z is a root
-/
lemma linear_two_roots_implies_trivial (e f : ℂ)
    (z1 z2 : ℂ) (hdist : z1 ≠ z2)
    (h1 : e * z1 + f = 0)
    (h2 : e * z2 + f = 0) :
    e = 0 ∧ f = 0 := by
  have hsub : e * z1 + f - (e * z2 + f) = 0 := by rw [h1,h2]; ring
  have : e * (z1 - z2) = 0 := by {
    rw [mul_sub]
    ring_nf at hsub
    exact hsub
  }
  have he : e = 0 := by
    by_contra hne
    have : z1 - z2 = 0 := by
      have := mul_eq_zero.mp this
      exact this.resolve_left hne
    exact hdist (sub_eq_zero.mp this)
  have hf : f = 0 := by
      calc f = e * z1 + f := by rw [he]; ring_nf
         _ = 0 := h1
  exact ⟨he , hf⟩


/- Helper lemmas
-/

/--
  Case 1: If all three fixed points of T are finite,
  then T is the identity function
-/
lemma fixes_three_finite_is_id (T : LinearFracTrans) (z1 z2 z3 : ℂ)
    (hdist : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z1 ≠ z3)
    (hfix1 : T (EComplex.some z1) = EComplex.some z1)
    (hfix2 : T (EComplex.some z2) = EComplex.some z2)
    (hfix3 : T (EComplex.some z3) = EComplex.some z3) :
    FunEq T id := by
  have hdenom1 : T.c * z1 + T.d ≠ 0 := by
    intro h
    simp only [apply] at hfix1
    split_ifs at hfix1 with h1 h2
    · {
      rw [h1,zero_mul,zero_add] at h
      have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
      rw [h1,h,mul_zero,mul_zero,zero_sub] at det_not_zero
      rw[neg_ne_zero] at det_not_zero
      contradiction
      }
    · {
      have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
      push Not at h1 h2
      have : z1 * T.c ≠ -T.d :=by {
        contrapose! h2
        field_simp [h1]
        exact h2
      }
      rw[add_eq_zero_iff_neg_eq',mul_comm,Eq.comm] at h
      contradiction
      }
  have hdenom2 : T.c * z2 + T.d ≠ 0 := by
    intro h
    simp only [apply] at hfix2
    split_ifs at hfix2 with h1 h2
    · {
      rw [h1,zero_mul,zero_add] at h
      have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
      rw [h1,h,mul_zero,mul_zero,zero_sub] at det_not_zero
      rw[neg_ne_zero] at det_not_zero
      contradiction
      }
    · {
      have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
      push Not at h1 h2
      have : z2 * T.c ≠ -T.d :=by {
        contrapose! h2
        field_simp [h1]
        exact h2
      }
      rw[add_eq_zero_iff_neg_eq',mul_comm,Eq.comm] at h
      contradiction
      }
  have hdenom3 : T.c * z3 + T.d ≠ 0 := by
    intro h
    simp only [apply] at hfix3
    split_ifs at hfix3 with h1 h2
    · {
      rw [h1,zero_mul,zero_add] at h
      have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
      rw [h1,h,mul_zero,mul_zero,zero_sub] at det_not_zero
      rw[neg_ne_zero] at det_not_zero
      contradiction
      }
    · {
      have det_not_zero : T.a * T.d - T.b * T.c ≠ 0 := by exact T.determinant_ne_zero
      push Not at h1 h2
      have : z3 * T.c ≠ -T.d :=by {
        contrapose! h2
        field_simp [h1]
        exact h2
      }
      rw[add_eq_zero_iff_neg_eq',mul_comm,Eq.comm] at h
      contradiction
      }
  have hquad1 : T.c * z1^2 + (T.d - T.a) * z1 - T.b = 0 := by
    rw [finite_fixed_iff T z1 hdenom1] at hfix1
    exact hfix1
  have hquad2 : T.c * z2^2 + (T.d - T.a) * z2 - T.b = 0 := by
    rw [finite_fixed_iff T z2 hdenom2] at hfix2
    exact hfix2
  have hquad3 : T.c * z3^2 + (T.d - T.a) * z3 - T.b = 0 := by
    rw [finite_fixed_iff T z3 hdenom3] at hfix3
    exact hfix3
  have hc : T.c = 0 := by
    by_contra hc_ne
    exact quadratic_at_most_two_roots T.c (T.d - T.a) (-T.b) hc_ne
      z1 z2 z3 hdist hquad1 hquad2 hquad3
  have hlin1 : (T.d - T.a) * z1 - T.b = 0 := by
    simp only [hc,zero_mul,zero_add] at hquad1
    exact hquad1
  have hlin2 : (T.d - T.a) * z2 - T.b = 0 := by
    simp only [hc, zero_mul, zero_add] at hquad2
    exact hquad2
  have hcoeffs : T.d - T.a = 0 ∧ T.b = 0 := by
    rw [sub_eq_add_neg] at hlin1
    rw [sub_eq_add_neg] at hlin2
    have : T.d - T.a = 0 ∧ -T.b = 0 := by {
      apply linear_two_roots_implies_trivial (T.d - T.a) (-T.b) z1 z2 hdist.1 hlin1 hlin2
    }
    rcases this with ⟨h1,h2⟩
    constructor
    exact h1
    exact neg_eq_zero.mp h2
  have ha : T.a = T.d := by {
    rcases hcoeffs with ⟨h1,h2⟩
    rw [sub_eq_zero,Eq.comm] at h1
    exact h1
  }
  have hb : T.b = 0 := by {
    rcases hcoeffs with ⟨h1,h2⟩
    exact h2
  }
  exact coeff_id_implies_fun_id T hc ha hb

/--
 Case 2: Suppose ∞ is one of the fixed points.
 If T(∞) = ∞, then c = 0, so T(z) = (az + b)/d
 Then T(z) = z means az + b = dz, i.e., (a - d)z + b = 0
-/
lemma fixes_infty_and_two_finite_is_id (T : LinearFracTrans) (z1 z2 : ℂ)
    (hdist : z1 ≠ z2)
    (hfix_infty : T none = none)
    (hfix1 : T (EComplex.some z1) = EComplex.some z1)
    (hfix2 : T (EComplex.some z2) = EComplex.some z2) :
    FunEq T id := by
    have hc : T.c = 0 := by exact (infty_fixed_iff T).mp hfix_infty
    have hd_ne : T.d ≠ 0 := fun hd => T.determinant_ne_zero (by simp [hc, hd])
    have hd1 : T.c * z1 + T.d ≠ 0 := by simp [hc, hd_ne]
    have hd2 : T.c * z2 + T.d ≠ 0 := by simp [hc,hd_ne]
    have h1 : (T.d - T.a) * z1 = T.b := by
      have := (finite_fixed_iff T z1 hd1).mp hfix1
      simp only [hc, zero_mul, zero_add] at this
      rw [sub_eq_zero] at this
      exact this
    have h2 : (T.d - T.a) * z2 = T.b := by
      have := (finite_fixed_iff T z2 hd2).mp hfix2
      simp only [hc, zero_mul, zero_add] at this
      rw [sub_eq_zero] at this
      exact this
    have ha : T.a = T.d := by
      by_contra hne
      have : z1 = z2 := by
        field_simp[sub_ne_zero.mpr (Ne.symm hne)] at h1 h2
        have eq : (T.d - T.a) * z1 = (T.d - T.a) * z2 := by rw [h1, h2]
        have : (T.d - T.a) * (z1 - z2) = 0 := by rw [mul_sub, eq, sub_self]
        have hneq : T.d - T.a ≠ 0 := by
          contrapose! hne
          rw [sub_eq_zero,Eq.comm] at hne
          exact hne
        rw [propext (mul_eq_zero_iff_left hneq),sub_eq_zero] at this
        exact this
      exact hdist this
    have hb : T.b = 0 := by
      simp only [ha, sub_self, zero_mul] at h1
      rw[Eq.comm]
      exact h1
    intro z
    cases z with
    | none => {
      simp [apply,hc, LinearFracTrans.id]
    }
    | some z => {
      simp only [apply,LinearFracTrans.id]
      simp only [hc,zero_mul,zero_add,ha,hb,add_zero]
      simp
      field_simp
    }


/-- Key lemma:
  LFT fixing three distinct points is the identity
  If T(zᵢ) = zᵢ for three distinct points, then T is the identity
 -/
lemma fixes_three_is_id (f : LinearFracTrans) (z1 z2 z3 : EComplex)
    (hz : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z3 ≠ z1)
    (hfix1 : f z1 = z1)
    (hfix2 : f z2 = z2)
    (hfix3 : f z3 = z3) :
    f.FunEq id := by
  cases z1 with
  | some z1 => {
    cases z2 with
    | some z2 => {
      cases z3 with
      | some z3 => {
        apply fixes_three_finite_is_id f z1 z2 z3
        · exact ⟨mt (congrArg EComplex.some) hz.1,
           mt (congrArg EComplex.some) hz.2.1,
           (mt (congrArg EComplex.some) hz.2.2.symm)⟩
        · exact hfix1
        · exact hfix2
        · exact hfix3
      }
      | none => {
        apply fixes_infty_and_two_finite_is_id f z1 z2
        · exact mt (congrArg EComplex.some) hz.1
        · exact hfix3
        · exact hfix1
        · exact hfix2
      }
    }
    | none => {
      cases z3 with
      | some z3 => {
        apply fixes_infty_and_two_finite_is_id f z1 z3
        · exact mt (congrArg EComplex.some) hz.2.2.symm
        · exact hfix2
        · exact hfix1
        · exact hfix3
      }
      | none => {
        rcases hz with ⟨h1,h2,h3⟩
        contradiction
      }
    }
  }
  | none => {
    cases z2 with
    | some z2 => {
      cases z3 with
      | some z3 => {
        apply fixes_infty_and_two_finite_is_id f z2 z3
        · exact mt (congrArg EComplex.some) hz.2.1
        · exact hfix1
        · exact hfix2
        · exact hfix3
      }
      | none => {
        rcases hz with ⟨h1,h2,h3⟩
        contradiction
      }
    }
    | none => {
      cases z3 with
      | some z3 => {
        rcases hz with ⟨h1,h2,h3⟩
        contradiction
      }
      | none => {
        rcases hz with ⟨h1,h2,h3⟩
        contradiction
      }
    }
  }

/--  #### Theorem 2.4.1
  If an LFT f(z) fixes 0, 1 and ∞,
  then f(z) is the identity function.
-/
lemma fixes_zero_one_infinity_id (f : LinearFracTrans)
    (hfix1 : f 0 = 0) (hfix2 : f 1 = 1) (hfix3 : f ∞ = ∞):
    f.FunEq id := by
  let z1 := (0 : EComplex)
  let z2 := (1 : EComplex)
  let z3 := (∞ : EComplex)
  have hz : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z3 ≠ z1 := by
    constructor
    · -- Show 0 ≠ 1
      intro h
      -- Reveal the underlying Option types
      change EComplex.some (0 : ℂ) = EComplex.some (1 : ℂ) at h
      -- Extract the equality of the inner values
      injection h with heq
      -- Use standard complex number inequality (0 ≠ 1)
      exact zero_ne_one heq
    · constructor
      · -- Show 1 ≠ ∞
        intro h
        change EComplex.some (1 : ℂ) = Option.none at h
        -- `injection` automatically closes goals
        injection h
      · -- Show ∞ ≠ 0
        intro h
        change Option.none = EComplex.some (0 : ℂ) at h
        injection h
  exact fixes_three_is_id f 0 1 ∞ hz hfix1 hfix2 hfix3




/-- Theorem 2.4.3 (uniqueness part)
 Main theorem: Uniqueness of LFT determined by three points
 If f and g agree on three distinct points, they agree everywhere
-/
theorem lft_uniqueness (f g : LinearFracTrans) (z1 z2 z3 : EComplex)
    (hdist : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z3 ≠ z1)
    (h1 : f z1 = g z1)
    (h2 : f z2 = g z2)
    (h3 : f z3 = g z3) :
    FunEq f g := by
  -- Strategy: show that g⁻¹ ∘ f fixes z₁, z₂, z₃
  -- Then by fixes_three_is_id, g⁻¹ ∘ f = id
  -- Therefore f = g
  let h := comp (inv g) f
  have hfix1 : h z1 = z1 := by
    simp only [h]
    rw [comp_apply,h1,← comp_apply,lft_mul_left_inv]
    exact id_apply z1
  have hfix2 : h z2 = z2 := by
    simp only [h]
    rw [comp_apply,h2,← comp_apply,lft_mul_left_inv]
    exact id_apply z2
  have hfix3 : h z3 = z3 := by
    simp only [h]
    rw [comp_apply,h3,← comp_apply,lft_mul_left_inv]
    exact id_apply z3
  have h_is_id : FunEq h id := fixes_three_is_id h z1 z2 z3 hdist hfix1 hfix2 hfix3
  intro z
  have : h z = LinearFracTrans.id z := h_is_id z
  simp only [h,comp_apply,id_apply] at this
  calc f z
      = g.apply ((inv g).apply (f.apply z))
       := by rw [← comp_apply,lft_mul_right_inv,id_apply]
    _ = g.apply z := by rw [this]



/-- #### Theorem 2.4.3 (Combined Existence and Uniqueness)
  Given any three distinct points z1, z2 and z3 and any
  three distinct points w1, w2 and w3, all in the extended
  complex plane EComplex, there is a unique linear
  fractional transformation that maps z1 to w1, z2 to w2,
  and z3 to w3.
-/
theorem exists_unique_lft_map_three_points
  (z1 z2 z3 w1 w2 w3 : EComplex)
  (hz : z1 ≠ z2 ∧ z2 ≠ z3 ∧ z3 ≠ z1)
  (hw : w1 ≠ w2 ∧ w2 ≠ w3 ∧ w3 ≠ w1) :
  ∃ f : LinearFracTrans,
    f z1 = w1 ∧  f z2 = w2 ∧ f z3 = w3 ∧
    ∀ g : LinearFracTrans, g z1 =w1 → g z2 =w2 → g z3 =w3
     → FunEq f g := by
  -- 1. Extract the existence of the mapping `f` from the
  -- existence theorem
  have ⟨f, hf1, hf2, hf3⟩
    := exists_lft_map_three_points z1 z2 z3 w1 w2 w3 hz hw

  -- 2. Provide `f` as the witness for the
  -- existential quantifier
  use f

  -- 3. The first three goals are just the properties
  -- of `f`, which we already have.
  -- For the uniqueness part, we introduce another LFT
  -- `g` and its properties.
  refine ⟨hf1, hf2, hf3, fun g hg1 hg2 hg3 => ?_⟩

  -- 4. Apply the uniqueness theorem
  apply lft_uniqueness f g z1 z2 z3 hz

  -- 5. Prove that f and g agree on z1, z2, and z3
  · exact hf1.trans hg1.symm
  · exact hf2.trans hg2.symm
  · exact hf3.trans hg3.symm

end LFT_fixed_point_property
