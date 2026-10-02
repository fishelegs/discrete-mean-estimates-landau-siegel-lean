import ZhangLS.Spec.Lemma55FullZeroExclusion

/-! Expanded original statement with actual mathlib L-functions, the
full original zero region, uniform constants and threshold. Additional
checks retain both closed height endpoints, all detection degrees,
actual multiplicities and distinct tags when heights coincide. -/

open Complex Finset Set ZhangLS.Spec
open scoped ComplexOrder

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

example : Lemma55Target := lemma55_proved

example : 0 < (64 : ℝ) ∧ ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∃ β : ℝ, 0 < 1 - β ∧ 1 - β ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ) ∧
        (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) (β : ℂ) = 0 ∧
        deriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) (β : ℂ) ≠ 0 ∧
        ∀ s : ℂ, (1 - 2 / Real.log (D : ℝ) < s.re ∧ |s.im| < 2 * (D : ℝ)) →
          (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) s = 0 → s = (β : ℂ) :=
  lemma55_at_constant_sixty_four

example {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) (n : ℕ) :
    (((-1 : ℂ) ^ n * iteratedDeriv n
      (logDeriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi))
        (lemma55JensenCenter t)) / (n.factorial : ℂ)) =
      -LSeries (LSeries.logMul^[n] (lemma55MangoldtTwist χ)) (lemma55JensenCenter t) /
        (n.factorial : ℂ) := lemma55_actual_normalized_logDeriv_mangoldt χ t n

example {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) (n : ℕ) :
    (lemma55NormalizedLogDerivative χ 0 n + lemma55ZetaNormalizedLogDerivative 0 n +
      (lemma55NormalizedLogDerivative χ t n + lemma55ZetaNormalizedLogDerivative t n)).re ≤ 0 :=
  lemma55_actual_four_logDeriv_nonpos χ t n

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) (β : ℂ) :
    (∑ a ∈ lemma55FourZeroFinset χ (2 * (D : ℝ)) β, (lemma55FamilyOrder χ a.1 a.2 : ℝ)) ≤
      62 * Real.log (D : ℝ) := lemma55_actual_four_zero_order_sum_bound χ hD hL (by simp) β

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {β r : ℝ}
    (hβ : β ≤ 1) (hzero : (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) (β : ℂ) = 0)
    (hderiv : deriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) (β : ℂ) ≠ 0)
    (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r) {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    (lemma55CombinedRemainingPower χ (-(2 * (D : ℝ))) r (β : ℂ) v J).re ≤
      374400 * Real.log (D : ℝ) + 8 +
        4 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ)) :=
  lemma55_actual_combined_remaining_real_upper_bound χ hD hL (by simp) hβ hzero hderiv hr hlower hv J

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {ρ β : ℂ}
    (hre : 1 - 2 / Real.log (D : ℝ) < ρ.re) (him : |ρ.im| < 2 * (D : ℝ))
    (hzero : (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) ρ = 0) (hne : ρ ≠ β) :
    ∃ a₀ ∈ lemma55FourZeroFinset χ ρ.im β,
      0 < ‖lemma55TaggedInverseSquare ρ.im a₀‖ ∧ ‖lemma55TaggedInverseSquare ρ.im a₀‖ < 1 ∧
      ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ ‖lemma55TaggedInverseSquare ρ.im a₀‖ ∧
      ∀ J : ℕ, (J : ℝ) / 4 - 62 * Real.log (D : ℝ) ≤
        (lemma55CombinedRemainingPower χ ρ.im ‖lemma55TaggedInverseSquare ρ.im a₀‖ β
          (lemma55TaggedInverseSquare ρ.im a₀ / (‖lemma55TaggedInverseSquare ρ.im a₀‖ : ℂ))⁻¹ J).re :=
  lemma55_original_other_zero_four_detected χ hD hL ⟨hre, him⟩ hzero hne

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) {ρ : ℂ}
    (hρ : ρ ∈ lemma55ExceptionalRemovedLocalZeros χ 0 β) :
    (⟨0, ρ⟩ : Lemma55TaggedZero) ∈ lemma55FourZeroFinset χ 0 β ∧
      (⟨2, ρ⟩ : Lemma55TaggedZero) ∈ lemma55FourZeroFinset χ 0 β ∧
      (⟨0, ρ⟩ : Lemma55TaggedZero) ≠ ⟨2, ρ⟩ := by
  classical
  constructor
  · exact (lemma55_mem_four_zero_finset χ 0 β ⟨0, ρ⟩).mpr hρ
  constructor
  · exact (lemma55_mem_four_zero_finset χ 0 β ⟨2, ρ⟩).mpr hρ
  · intro h
    have ht := congrArg Sigma.fst h
    exact (by decide : (0 : Fin 4) ≠ 2) ht

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (t r : ℝ) (v : ℂ) :
    lemma55CombinedRemainingPower χ t r β v 0 = 0 := by
  simp [lemma55CombinedRemainingPower, lemma55WeightedRemainingZeroPowerSum, lemma55ZetaWeightedZeroPowerSum]

example {L δ : ℝ} (hL : 2000 ≤ L) (hC : lemma55RepulsionErrorConstant ≤ L)
    (hδ : 0 ≤ δ) (hclose : δ ≤ 64 * L ^ (-2022 : ℤ)) :
    374400 * L + 8 + 4 * δ * (lemma55RepulsionDegree L : ℝ) * ((lemma55RepulsionDegree L : ℝ) + 1) *
      Real.exp (4 * (lemma55RepulsionDegree L : ℝ) / L) < (lemma55RepulsionDegree L : ℝ) / 4 - 62 * L :=
  lemma55_repulsion_strict_budget hL hC hδ hclose

#print axioms lemma55_actual_mangoldt_twist_summable
#print axioms lemma55_actual_mangoldt_abscissa
#print axioms lemma55_actual_logDeriv_mangoldt
#print axioms lemma55_actual_higher_logDeriv_mangoldt
#print axioms lemma55_actual_normalized_logDeriv_mangoldt
#print axioms lemma55_actual_zeta_normalized_mangoldt
#print axioms lemma55_nonnegative_series_height_bound
#print axioms lemma55_nonnegative_series_two_heights
#print axioms lemma55_mangoldt_trivial
#print axioms lemma55_actual_mangoldt_positive
#print axioms lemma55_log_power_nonnegative
#print axioms lemma55_log_power_add
#print axioms lemma55_actual_log_power_summable
#print axioms lemma55_actual_combined_mangoldt_summable
#print axioms lemma55_actual_two_function_mangoldt
#print axioms lemma55_actual_four_logDeriv_nonpos
#print axioms lemma55_actual_weighted_four_logDeriv_nonpos
#print axioms lemma55_distant_inverse_square_ratio
#print axioms lemma55_distant_geometric_sum_bound
#print axioms lemma55_distant_weighted_kernel_bound
#print axioms lemma55_actual_exceptional_outside_local_disk_distance
#print axioms lemma55_actual_exceptional_outside_local_disk_tail_bound
#print axioms lemma55_actual_combined_remaining_error_bound
#print axioms lemma55_actual_removed_pair_pole_identity
#print axioms lemma55_actual_combined_removed_derivative_nonpos
#print axioms lemma55_actual_local_pole_difference_eq
#print axioms lemma55_actual_local_pole_difference_bound
#print axioms lemma55_actual_combined_remaining_real_upper_bound
#print axioms lemma55_mem_four_zero_finset
#print axioms lemma55_actual_zeta_inverse_square_norm_bounds
#print axioms lemma55_actual_tagged_zero_order_pos
#print axioms lemma55_actual_tagged_inverse_square_bounds
#print axioms lemma55_removed_zero_order_sum_bound
#print axioms lemma55_actual_four_zero_order_sum_bound
#print axioms lemma55_actual_tagged_power_sum_eq
#print axioms lemma55_tagged_normalized_power_sum
#print axioms lemma55_actual_weighted_tagged_power_sum_eq
#print axioms lemma55_actual_weighted_tagged_real_sum_eq
#print axioms lemma55_original_other_zero_in_four_families
#print axioms lemma55_actual_common_maximum_weighted_detection
#print axioms lemma55_original_other_zero_four_detected
#print axioms lemma55_repulsion_error_constant_pos
#print axioms lemma55_repulsion_degree_bounds
#print axioms lemma55_repulsion_exponential_cost
#print axioms lemma55_repulsion_exceptional_cost_bound
#print axioms lemma55_repulsion_strict_budget
#print axioms lemma55_uniform_repulsion_modulus_threshold
#print axioms lemma55_actual_full_zero_exclusion
#print axioms lemma55_at_constant_sixty_four
#print axioms lemma55_proved
