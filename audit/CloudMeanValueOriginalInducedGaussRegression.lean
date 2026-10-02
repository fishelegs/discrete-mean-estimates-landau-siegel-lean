import ZhangLS.Spec.InducedGaussMainCharacters
set_option autoImplicit false
open ZhangLS.Spec Complex DirichletCharacter

example {r h : ℕ} [NeZero r] [NeZero h] (χ : DirichletCharacter ℂ r) :
    letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
    gaussSum (χ.changeLevel (r.dvd_mul_right h)) ZMod.stdAddChar =
      (ArithmeticFunction.moebius h:ℂ)*χ (h:ZMod r)*gaussSum χ ZMod.stdAddChar :=
  inducedGauss_changeLevel_formula χ

example {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) :
    ‖gaussSum θ⁻¹ ZMod.stdAddChar‖≤Real.sqrt (θ.conductor:ℝ) :=
  inducedGauss_inverse_norm_le_sqrt_conductor θ

example : gaussSum (1:DirichletCharacter ℂ 1) ZMod.stdAddChar=1 :=
  inducedGauss_level_one_value _

example : ‖gaussSum (1:DirichletCharacter ℂ 1) ZMod.stdAddChar‖=Real.sqrt (1:ℝ) := by
  rw [inducedGauss_level_one_value]
  norm_num

example (χ : DirichletCharacter ℂ 3) :
    gaussSum (χ.changeLevel (by norm_num : 3∣9)) ZMod.stdAddChar=0 := by
  have he := inducedGauss_changeLevel_formula (h := 3) χ
  have hz : χ ((3:ℕ):ZMod 3)=0 :=
    MulChar.map_nonunit χ (by
      rw [ZMod.isUnit_iff_coprime]
      decide)
  rw [hz,mul_zero,zero_mul] at he
  exact he

example {D k : ℕ} [NeZero k] (χ : RealPrimitiveCharacter D)
    (p l : ℕ) (hp : p.Coprime k) (hl : l.Coprime k) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
    let θ := χ.chi.changeLevel (D.dvd_mul_right k)
    gaussSum θ⁻¹ ZMod.stdAddChar*θ (-(l:ZMod (D*k)))*θ⁻¹ (p:ZMod (D*k)) =
      (ArithmeticFunction.moebius k:ℂ)*χ.chi (k:ZMod D)*gaussSum χ.chi ZMod.stdAddChar*
        χ.chi (-(p:ZMod D)*(l:ZMod D)) := inducedGauss_real_phase_product χ p l hp hl
-- GENERATED AXIOM CHECKS
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_formula_dvd
#print axioms ZhangLS.Spec.inducedGauss_conductor_formula
#print axioms ZhangLS.Spec.inducedGauss_level_one_value
#print axioms ZhangLS.Spec.inducedGauss_primitive_norm
#print axioms ZhangLS.Spec.inducedGauss_mobius_norm_le_one
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_norm_le
#print axioms ZhangLS.Spec.inducedGauss_norm_le_sqrt_conductor
#print axioms ZhangLS.Spec.inducedGauss_inverse_norm_le_sqrt_conductor
#print axioms ZhangLS.Spec.inducedGauss_nonprincipal_conductor_gt_one
#print axioms ZhangLS.Spec.inducedGauss_sum_zmod_eq_range
#print axioms ZhangLS.Spec.inducedGauss_sum_range_multiples
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_nat
#print axioms ZhangLS.Spec.inducedGauss_mobius_indicator
#print axioms ZhangLS.Spec.inducedGauss_mobius_indicator_divisors
#print axioms ZhangLS.Spec.inducedGauss_scaled_additive
#print axioms ZhangLS.Spec.inducedGauss_coprime_sum_mobius
#print axioms ZhangLS.Spec.inducedGauss_divisor_inner
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_formula
#print axioms ZhangLS.Spec.inducedGaussInflation
#print axioms ZhangLS.Spec.inducedGauss_inflation_zero
#print axioms ZhangLS.Spec.inducedGauss_inflation_one
#print axioms ZhangLS.Spec.inducedGauss_inflation_formula
#print axioms ZhangLS.Spec.inducedGauss_principal_value
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_neg_nat
#print axioms ZhangLS.Spec.inducedGauss_phase_product
#print axioms ZhangLS.Spec.inducedGauss_real_changeLevel_inv
#print axioms ZhangLS.Spec.inducedGauss_real_phase_product
#print axioms ZhangLS.Spec.inducedGauss_totient_denominator
#print axioms ZhangLS.Spec.inducedGauss_coprime_filter
#print axioms ZhangLS.Spec.inducedGauss_real_square

#print ZhangLS.Spec.inducedGauss_changeLevel_formula
#print ZhangLS.Spec.inducedGauss_inverse_norm_le_sqrt_conductor
