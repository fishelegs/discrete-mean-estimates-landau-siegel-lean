import ZhangLS.Spec.InducedGaussFormula

/-! # Actual induced Gauss formula at the primitive conductor

The primitive conductor and unit-domain distinction are genuine. Principal
conductor one is included in the Gauss norm identity; the nonprincipal
restriction for Lemma5.6 remains a separate, explicit arithmetic fact.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

/-- The formula at an arbitrary target modulus, not only a displayed product. -/
theorem inducedGauss_changeLevel_formula_dvd {r N : ℕ} [NeZero r] [NeZero N]
    (χ : DirichletCharacter ℂ r) (hrN : r∣N) :
    gaussSum (χ.changeLevel hrN) ZMod.stdAddChar =
      (ArithmeticFunction.moebius (N/r):ℂ)*χ ((N/r:ℕ):ZMod r)*gaussSum χ ZMod.stdAddChar := by
  obtain ⟨h,rfl⟩ := hrN
  have hhp : 0<h := by
    have hz := NeZero.ne (r*h)
    by_contra hh
    have he : h=0 := by omega
    exact hz (by rw [he,mul_zero])
  letI : NeZero h := ⟨hhp.ne'⟩
  have hquot : r*h/r=h := Nat.mul_div_cancel_left h (Nat.pos_of_ne_zero (NeZero.ne r))
  simpa only [hquot] using inducedGauss_changeLevel_formula (h := h) χ

/-- The actual level-N character is recovered from its genuine primitive
inducer before applying the formula. -/
theorem inducedGauss_conductor_formula {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) :
    letI : NeZero θ.conductor := ⟨θ.conductor_ne_zero⟩
    gaussSum θ ZMod.stdAddChar =
      (ArithmeticFunction.moebius (N/θ.conductor):ℂ)*
        θ.primitiveCharacter ((N/θ.conductor:ℕ):ZMod θ.conductor)*
          gaussSum θ.primitiveCharacter ZMod.stdAddChar := by
  letI : NeZero θ.conductor := ⟨θ.conductor_ne_zero⟩
  have hh := inducedGauss_changeLevel_formula_dvd θ.primitiveCharacter θ.conductor_dvd_level
  rwa [changeLevel_primitiveCharacter] at hh

/-- The residue-zero term is handled explicitly at modulus one. -/
theorem inducedGauss_level_one_value (χ : DirichletCharacter ℂ 1) :
    gaussSum χ ZMod.stdAddChar=1 := by
  have he (a : ZMod 1) : χ a*ZMod.stdAddChar a=1 := by
    have ha : a=1 := Subsingleton.elim _ _
    have hz : a=0 := Subsingleton.elim _ _
    rw [ha,map_one]
    rw [show (1:ZMod 1)=0 by exact Subsingleton.elim _ _,AddChar.map_zero_eq_one]
    simp
  simp only [gaussSum,he,sum_const,card_univ,ZMod.card,nsmul_eq_mul,Nat.cast_one,one_mul]

/-- Primitive Gauss norm, including the principal primitive modulus one. -/
theorem inducedGauss_primitive_norm {r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖=Real.sqrt (r:ℝ) := by
  by_cases hr : r=1
  · subst r
    rw [inducedGauss_level_one_value]
    norm_num
  · have hh := lemma23_rootNumber_norm_eq_one χ hχ hr
    rw [DirichletCharacter.rootNumber] at hh
    simp only [norm_div,norm_pow,Complex.norm_I,one_pow,div_one] at hh
    have hrp : 0<r := Nat.pos_of_ne_zero (NeZero.ne r)
    have hden : ‖(r:ℂ)^((1/2):ℂ)‖=Real.sqrt (r:ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hrp]
      norm_num [Real.sqrt_eq_rpow]
    rw [hden] at hh
    have hpos : 0<Real.sqrt (r:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hrp)
    exact (div_eq_one_iff_eq hpos.ne').mp hh

theorem inducedGauss_mobius_norm_le_one (h : ℕ) : ‖(ArithmeticFunction.moebius h:ℂ)‖≤1 := by
  rcases ArithmeticFunction.moebius_eq_or h with hz | hz | hz <;> rw [hz] <;> norm_num

/-- Induction never enlarges the Gauss amplitude; the nonunit h branch is
included via the character's actual zero values. -/
theorem inducedGauss_changeLevel_norm_le {r N : ℕ} [NeZero r] [NeZero N]
    (χ : DirichletCharacter ℂ r) (hrN : r∣N) :
    ‖gaussSum (χ.changeLevel hrN) ZMod.stdAddChar‖≤‖gaussSum χ ZMod.stdAddChar‖ := by
  rw [inducedGauss_changeLevel_formula_dvd χ hrN,norm_mul,norm_mul]
  have hh : ‖(ArithmeticFunction.moebius (N/r):ℂ)‖*‖χ ((N/r:ℕ):ZMod r)‖≤1 :=
    mul_le_one₀ (inducedGauss_mobius_norm_le_one _) (norm_nonneg _) (χ.norm_le_one _)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (norm_nonneg (gaussSum χ ZMod.stdAddChar))

/-- The needed imprimitive estimate is about the ACTUAL conductor. -/
theorem inducedGauss_norm_le_sqrt_conductor {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) :
    ‖gaussSum θ ZMod.stdAddChar‖≤Real.sqrt (θ.conductor:ℝ) := by
  letI : NeZero θ.conductor := ⟨θ.conductor_ne_zero⟩
  have hh := inducedGauss_changeLevel_norm_le θ.primitiveCharacter θ.conductor_dvd_level
  rw [changeLevel_primitiveCharacter,inducedGauss_primitive_norm θ.primitiveCharacter
    θ.primitiveCharacter_isPrimitive] at hh
  exact hh

/-- Precisely the conjugated Gauss amplitude appearing in (7.13)/(14.8). -/
theorem inducedGauss_inverse_norm_le_sqrt_conductor {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) :
    ‖gaussSum θ⁻¹ ZMod.stdAddChar‖≤Real.sqrt (θ.conductor:ℝ) := by
  have hh := inducedGauss_norm_le_sqrt_conductor θ⁻¹
  rwa [conductor_inv] at hh

/-- The nonprincipal original θ has conductor>1. This is never inferred
merely from a name displayed on its primitive inducer. -/
theorem inducedGauss_nonprincipal_conductor_gt_one {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ≠1) : 1<θ.conductor := by
  have hzero := θ.conductor_ne_zero
  have hone : θ.conductor≠1 := fun hh => hθ (eq_one_iff_conductor_eq_one.mpr hh)
  omega

end ZhangLS.Spec
