import ZhangLS.Spec.Lemma55ExceptionalZeroRemoval

/-! Closed unit-disk boundary, actual L-function derivative jets, both
height endpoints, unbounded finite detection degree, exact removal of
the actual simple zero, and candidates in the entire original region.
These checks do not assert complete original-region zero exclusion. -/

open Complex Finset Set ZhangLS.Spec

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

example (J : ℕ) : -(1 : ℝ) / 2 ≤ lemma55FejerKernel I J :=
  lemma55_fejer_kernel_lower_bound (by simp) J

example (J : ℕ) : lemma55FejerKernel 1 J = (J : ℝ) / 2 :=
  lemma55_fejer_kernel_at_one J

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t) =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) *
        ∑ ρ ∈ lemma55LocalZeroFinset χ t,
          (analyticOrderNatAt (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) ρ : ℂ) /
            (lemma55JensenCenter t - ρ) ^ (n + 1) :=
  lemma55_actual_local_zero_higher_derivative χ hD t n

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) (n : ℕ) :
    ‖((-1 : ℂ) ^ n * iteratedDeriv n
        (logDeriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi))
          (lemma55JensenCenter (2 * (D : ℝ)))) / (n.factorial : ℂ) -
      ∑ ρ ∈ lemma55LocalZeroFinset χ (2 * (D : ℝ)),
        (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) /
          (lemma55JensenCenter (2 * (D : ℝ)) - ρ) ^ (n + 1)‖ ≤
        990 * ((n : ℝ) + 1) * Real.log (D : ℝ) * (8 / 9 : ℝ) ^ (n + 1) :=
  lemma55_actual_power_sum_remainder_bound χ hD hL (by simp) n

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {r : ℝ} (hr : 0 < r)
    (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedLogDerivative χ (2 * (D : ℝ)) r v J -
      lemma55WeightedZeroPowerSum χ (2 * (D : ℝ)) r v J‖ ≤ 79200 * Real.log (D : ℝ) :=
  lemma55_actual_weighted_power_error_uniform_bound χ hD hL (by simp) hr hlower hv J

example {D : ℕ} (χ : RealPrimitiveCharacter D) (t r : ℝ) (v : ℂ) :
    lemma55WeightedLogDerivative χ t r v 0 = 0 ∧ lemma55WeightedZeroPowerSum χ t r v 0 = 0 := by
  simp [lemma55WeightedLogDerivative, lemma55WeightedZeroPowerSum]

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) {β : ℂ}
    (hzero : (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) β = 0)
    (hderiv : deriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) β ≠ 0) (k : ℕ) :
    (∑ ρ ∈ lemma55ExceptionalRemovedLocalZeros χ t β,
      (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) / (lemma55JensenCenter t - ρ) ^ k) =
        lemma55LocalZeroPowerSum χ t k -
          (if β ∈ lemma55LocalZeroFinset χ t then 1 / (lemma55JensenCenter t - β) ^ k else 0) :=
  lemma55_actual_simple_zero_removed_power_sum χ hD t hzero hderiv k

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {r : ℝ} (hr : 0 < r)
    (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r) {β v : ℂ}
    (hzero : (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) β = 0)
    (hderiv : deriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) β ≠ 0)
    (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedRemovedLogDerivative χ (-(2 * (D : ℝ))) r β v J -
      lemma55WeightedRemainingZeroPowerSum χ (-(2 * (D : ℝ))) r β v J‖ ≤
        79200 * Real.log (D : ℝ) :=
  lemma55_actual_weighted_remaining_error_uniform_bound χ hD hL (by simp) hr hlower hzero hderiv hv J

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {ρ β : ℂ}
    (hre : 1 - 2 / Real.log (D : ℝ) < ρ.re) (him : |ρ.im| < 2 * (D : ℝ))
    (hzero : (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) ρ = 0) (hne : ρ ≠ β) :
    ∃ ρ₀ ∈ lemma55ExceptionalRemovedLocalZeros χ ρ.im β,
      0 < ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ ∧
      ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ < 1 ∧
      ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ ∧
      ∀ J : ℕ, (J : ℝ) / 4 - 13 * Real.log (D : ℝ) ≤
        (lemma55WeightedRemainingZeroPowerSum χ ρ.im ‖lemma55ZeroInverseSquare ρ.im ρ₀‖ β
          (lemma55ZeroInverseSquare ρ.im ρ₀ / (‖lemma55ZeroInverseSquare ρ.im ρ₀‖ : ℂ))⁻¹ J).re :=
  lemma55_original_other_zero_detected χ hD hL ⟨hre, him⟩ hzero hne

example (t : ℝ) {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r) {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedExceptionalPoleDifference t 1 r v J‖ ≤ 0 := by
  simpa using lemma55_weighted_exceptional_pole_difference_bound t 1 le_rfl hL hr hlower hv J

#print axioms lemma55_fejer_geom_rec
#print axioms lemma55_fejer_geom_norm_rec
#print axioms lemma55_fejer_positive_identity
#print axioms lemma55_fejer_nested_lower_bound
#print axioms lemma55_fejer_nested_eq_weighted
#print axioms lemma55_fejer_kernel_lower_bound
#print axioms lemma55_fejer_kernel_at_one
#print axioms lemma55_fejer_weight_nonneg
#print axioms lemma55_fejer_weight_le_one
#print axioms lemma55_fejer_kernel_eq_weighted
#print axioms lemma55_fejer_detector_lower_bound
#print axioms lemma55_fejer_detector_at_unit
#print axioms lemma55_fejer_detector_eq_weighted
#print axioms lemma55_fejer_detection_weight_bounds
#print axioms lemma55_fejer_finite_detection
#print axioms lemma55_fejer_finite_weighted_power_detection
#print axioms lemma55_iterated_deriv_inverse_pole
#print axioms lemma55_iterated_deriv_weighted_inverse_pole
#print axioms lemma55_actual_local_zero_higher_derivative
#print axioms lemma55_actual_power_sum_remainder_norm_eq
#print axioms lemma55_actual_power_sum_remainder_bound
#print axioms lemma55_actual_power_sum_remainder_sum_bound
#print axioms lemma55_actual_local_zero_center_distance
#print axioms lemma55_actual_inverse_square_norm_bounds
#print axioms lemma55_actual_subset_max_inverse_square
#print axioms lemma55_normalized_inverse_square_unit
#print axioms lemma55_normalized_inverse_square_le_one
#print axioms lemma55_normalized_inverse_square_power_sum
#print axioms lemma55_actual_subset_weighted_power_detection
#print axioms lemma55_actual_subset_weighted_detection_log_bound
#print axioms lemma55_jensen_center_at_zero_height
#print axioms lemma55_original_zero_in_own_local_disk
#print axioms lemma55_original_zero_inverse_square_lower_bound
#print axioms lemma55_original_candidate_subset_normalization
#print axioms lemma55_normalization_power_exp_bound
#print axioms lemma55_normalization_first_powers_exp_bound
#print axioms lemma55_actual_odd_power_remainder_sum_bound
#print axioms lemma55_weighted_complex_difference_bound
#print axioms lemma55_actual_weighted_power_error_bound
#print axioms lemma55_actual_weighted_real_power_error_bound
#print axioms lemma55_normalized_remainder_geometric_ratio
#print axioms lemma55_actual_normalized_odd_power_error_bound
#print axioms lemma55_successor_geometric_finite_bound
#print axioms lemma55_actual_weighted_power_error_uniform_bound
#print axioms lemma55_actual_weighted_real_power_error_uniform_bound
#print axioms lemma55_unit_disk_power_difference
#print axioms lemma55_real_pole_center_distance
#print axioms lemma55_real_pole_inverse_difference
#print axioms lemma55_real_pole_inverse_power_difference
#print axioms lemma55_sum_successors
#print axioms lemma55_weighted_exceptional_pole_difference_bound
#print axioms lemma55_actual_simple_zero_order_nat
#print axioms lemma55_actual_simple_zero_removed_power_sum
#print axioms lemma55_actual_removed_power_remainder_eq
#print axioms lemma55_actual_removed_power_remainder_sum_bound
#print axioms lemma55_original_other_zero_remaining_normalization
#print axioms lemma55_actual_weighted_remaining_remainder_eq
#print axioms lemma55_actual_weighted_remaining_error_uniform_bound
#print axioms lemma55_actual_weighted_remaining_detection
#print axioms lemma55_original_other_zero_detected
