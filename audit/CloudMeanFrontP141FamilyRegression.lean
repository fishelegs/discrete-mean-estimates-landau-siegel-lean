import ZhangLS.Spec.PrimitiveConductorGaussBound
set_option autoImplicit false
open ZhangLS.Spec DirichletCharacter Finset
open scoped Classical
example {N:ℕ} [NeZero N] (F:DirichletCharacter ℂ N→ℝ) :
    (∑θ:DirichletCharacter ℂ N,F θ)=
      ∑i:primitiveConductorFamilyIndex N,F (primitiveConductorFamilyLift N i) :=
  primitiveConductorFamily_sum F
example {N:ℕ} [NeZero N] (i:primitiveConductorFamilyIndex N) :
    (primitiveConductorFamilyLift N i).conductor=i.1.val :=
  primitiveConductorFamily_lift_conductor i
example (i:primitiveConductorFamilyIndex 1) : primitiveConductorFamilyLift 1 i=1 :=
  (primitiveConductorFamily_principal_iff i).mpr (Nat.dvd_one.mp (Nat.mem_divisors.mp i.1.property).1)
example (θ:DirichletCharacter ℂ 4) (hθ:θ.IsPrimitive) :
    (θ.changeLevel (by norm_num : 4∣8)).conductor=4 := by
  rw [lemma44_conductor_changeLevel θ]
  exact hθ
#print axioms ZhangLS.Spec.inducedGauss_sum_zmod_eq_range
#print axioms ZhangLS.Spec.inducedGauss_sum_range_multiples
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_nat
#print axioms ZhangLS.Spec.inducedGauss_mobius_indicator
#print axioms ZhangLS.Spec.inducedGauss_mobius_indicator_divisors
#print axioms ZhangLS.Spec.inducedGauss_scaled_additive
#print axioms ZhangLS.Spec.inducedGaussInflation
#print axioms ZhangLS.Spec.inducedGauss_inflation_zero
#print axioms ZhangLS.Spec.inducedGauss_inflation_one
#print axioms ZhangLS.Spec.inducedGauss_inflation_formula
#print axioms ZhangLS.Spec.inducedGauss_coprime_sum_mobius
#print axioms ZhangLS.Spec.inducedGauss_divisor_inner
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_formula
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_formula_dvd
#print axioms ZhangLS.Spec.inducedGauss_conductor_formula
#print axioms ZhangLS.Spec.inducedGauss_level_one_value
#print axioms ZhangLS.Spec.inducedGauss_primitive_norm
#print axioms ZhangLS.Spec.inducedGauss_mobius_norm_le_one
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_norm_le
#print axioms ZhangLS.Spec.inducedGauss_norm_le_sqrt_conductor
#print axioms ZhangLS.Spec.inducedGauss_inverse_norm_le_sqrt_conductor
#print axioms ZhangLS.Spec.inducedGauss_nonprincipal_conductor_gt_one
#print axioms ZhangLS.Spec.primitiveConductorFamilyIndex
#print axioms ZhangLS.Spec.primitiveConductorFamilyFintype
#print axioms ZhangLS.Spec.primitiveConductorFamilyLift
#print axioms ZhangLS.Spec.primitiveConductorFamily_index_pos
#print axioms ZhangLS.Spec.primitiveConductorFamily_lift_conductor
#print axioms ZhangLS.Spec.primitiveConductorFamily_lift_injective
#print axioms ZhangLS.Spec.primitiveConductorFamily_lift_surjective
#print axioms ZhangLS.Spec.primitiveConductorFamilyEquiv
#print axioms ZhangLS.Spec.primitiveConductorFamily_sum
#print axioms ZhangLS.Spec.primitiveConductorFamily_sum_divisors
#print axioms ZhangLS.Spec.primitiveConductorFamily_filtered_sum
#print axioms ZhangLS.Spec.primitiveConductorFamily_principal_iff
#print axioms ZhangLS.Spec.primitiveConductorFamily_two_exclusions_sum
#print axioms ZhangLS.Spec.primitiveConductorFamily_gauss_bound
#print axioms ZhangLS.Spec.primitiveConductorFamily_nonprincipal_gauss_bound
#print axioms ZhangLS.Spec.primitiveConductorFamily_two_exclusions_gauss_bound
