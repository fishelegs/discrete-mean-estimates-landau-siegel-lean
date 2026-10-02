import ZhangLS.Spec.Lemma55ZetaWeightedPowerError

/-! Actual zeta, its removed pole and actual analytic orders. Checks
include both closed height endpoints, all derivative and detection
orders, removable zero values, closed disk boundaries and J=0.
This regression does not claim original-region zero exclusion. -/

open Complex Metric Finset Set ZhangLS.Spec

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

example : dirichletLFunction lemma55ZetaTrivialCharacter = riemannZeta :=
  lemma55_zeta_trivial_L_eq

example : zetaPoleRemoved 1 = 1 := lemma55_actual_zeta_pole_removed_at_one

example (t : ℝ) : (1 : ℂ) ∉ lemma55ZetaLocalZeroFinset t := by
  intro h
  exact riemannZeta_one_ne_zero ((lemma55_mem_actual_zeta_local_zero_finset t 1).mp h).2

example (t : ℝ) : AnalyticOnNhd ℂ zetaPoleRemoved
    (closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :=
  lemma55_actual_zeta_disk_analytic t (3 / 2) le_rfl

example (t : ℝ) {z : ℂ} (hz : 0 < z.re) (hzero : riemannZeta z = 0) :
    lemma55ZetaLocalZeroFactor t z * lemma55ZetaZeroRemoved t z = 0 := by
  rw [← lemma55_actual_zeta_zero_factorization t hz]
  exact (lemma55_actual_zeta_pole_removed_zero_iff hz).mpr hzero

example {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ lemma55ZetaLocalZeroFinset t) :
    analyticOrderNatAt zetaPoleRemoved ρ = analyticOrderNatAt riemannZeta ρ :=
  lemma55_actual_zeta_local_zero_order_nat_eq hρ

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) :
    (∑ ρ ∈ lemma55ZetaLocalZeroFinset (2 * (D : ℝ)),
      (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ 18 * Real.log (D : ℝ) := by
  have h := lemma55_actual_zeta_local_multiplicity_bound hD hL (by simp : |2 * (D : ℝ)| ≤ 2 * D)
  unfold lemma55ZetaLocalMultiplicity at h
  push_cast at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [lemma55_actual_zeta_local_zero_order_nat_eq hρ]

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) (n : ℕ) :
    ‖((-1 : ℂ) ^ n * iteratedDeriv n (logDeriv riemannZeta)
        (lemma55JensenCenter (2 * (D : ℝ)))) / (n.factorial : ℂ) +
      1 / (lemma55JensenCenter (2 * (D : ℝ)) - 1) ^ (n + 1) -
      ∑ ρ ∈ lemma55ZetaLocalZeroFinset (2 * (D : ℝ)),
        (analyticOrderNatAt riemannZeta ρ : ℂ) /
          (lemma55JensenCenter (2 * (D : ℝ)) - ρ) ^ (n + 1)‖ ≤
        1350 * ((n : ℝ) + 1) * Real.log (D : ℝ) * (8 / 9 : ℝ) ^ (n + 1) := by
  have h := lemma55_actual_zeta_pole_corrected_power_error_bound (t := 2 * (D : ℝ)) hD hL (by simp) n
  rw [lemma55_actual_zeta_zero_power_sum_eq] at h
  exact h

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖(∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55ZetaNormalizedLogDerivative (-(2 * (D : ℝ))) (2 * j + 1) +
          1 / (lemma55JensenCenter (-(2 * (D : ℝ))) - 1) ^ (2 * (j + 1))) /
            (r : ℂ) ^ (j + 1)) -
      ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (∑ ρ ∈ lemma55ZetaLocalZeroFinset (-(2 * (D : ℝ))),
          (analyticOrderNatAt riemannZeta ρ : ℂ) /
            (lemma55JensenCenter (-(2 * (D : ℝ))) - ρ) ^ (2 * (j + 1))) /
              (r : ℂ) ^ (j + 1)‖ ≤ 108000 * Real.log (D : ℝ) := by
  have h := lemma55_actual_zeta_weighted_power_error_uniform_bound hD hL
    (by simp : |-(2 * (D : ℝ))| ≤ 2 * D) hr hlower hv J
  rw [lemma55_actual_zeta_weighted_pole_correction] at h
  unfold lemma55ZetaWeightedZeroPowerSum at h
  simp_rw [lemma55_actual_zeta_zero_power_sum_eq] at h
  exact h

example (t r : ℝ) (v : ℂ) :
    lemma55ZetaWeightedRemovedLogDerivative t r v 0 = 0 ∧
      lemma55ZetaWeightedZeroPowerSum t r v 0 = 0 := by
  simp [lemma55ZetaWeightedRemovedLogDerivative, lemma55ZetaWeightedZeroPowerSum]

example (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logDeriv zetaPoleRemoved) (lemma55JensenCenter t) =
      iteratedDeriv n (logDeriv riemannZeta) (lemma55JensenCenter t) +
        (-1 : ℂ) ^ n * (n.factorial : ℂ) *
          (lemma55JensenCenter t - 1) ^ (-1 - (n : ℤ)) :=
  lemma55_actual_zeta_pole_removed_higher_logDeriv t n

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    (S : Finset ℕ) :
    (∑ n ∈ S, ‖lemma55ZetaNormalizedRemovedLogDerivative 0 n -
      lemma55ZetaLocalZeroPowerSum 0 (n + 1)‖) ≤ 97200 * Real.log (D : ℝ) :=
  lemma55_actual_zeta_power_sum_remainder_sum_bound hD hL (by simp) S

#print axioms lemma55_actual_zeta_zero_removed_higher_logDeriv_bound
#print axioms lemma55_actual_zeta_higher_logDeriv_remainder_eq
#print axioms lemma55_actual_zeta_higher_logDeriv_remainder_bound
#print axioms lemma55_actual_zeta_normalized_logDeriv_remainder_bound
#print axioms lemma55_actual_zeta_logDeriv_remainder_sum_bound
#print axioms lemma55_zeta_trivial_L_eq
#print axioms lemma55_actual_zeta_norm_lower
#print axioms lemma55_actual_zeta_pole_removed_analyticAt
#print axioms lemma55_actual_zeta_pole_removed_at_one
#print axioms lemma55_actual_zeta_pole_removed_center_lower
#print axioms lemma55_actual_zeta_pole_removed_disk_bound
#print axioms lemma55_actual_zeta_pole_removed_zero_iff
#print axioms lemma55_actual_zeta_pole_removed_zero_re_lt_one
#print axioms lemma55_actual_zeta_pole_removed_order_finite
#print axioms lemma55_actual_zeta_pole_removed_logDeriv
#print axioms lemma55_actual_zeta_pole_removed_higher_logDeriv
#print axioms lemma55_actual_zeta_jensen_multiplicity_bound
#print axioms lemma55_actual_zeta_zero_factor_logDeriv
#print axioms lemma55_actual_zeta_removed_local_logDeriv_formula
#print axioms lemma55_actual_zeta_zero_removed_center_logDeriv_bound
#print axioms lemma55_actual_zeta_center_local_logDeriv_formula
#print axioms lemma55_actual_zeta_center_local_logDeriv_error
#print axioms lemma55_actual_zeta_right_analytic
#print axioms lemma55_zeta_disk_re_pos
#print axioms lemma55_actual_zeta_disk_analytic
#print axioms lemma55_actual_zeta_order_eq_removed
#print axioms lemma55_actual_zeta_order_nat_eq_removed
#print axioms lemma55_actual_zeta_local_divisor_eq_order
#print axioms lemma55_mem_actual_zeta_local_zero_finset
#print axioms lemma55_actual_zeta_local_zero_order_nat_eq
#print axioms lemma55_actual_zeta_local_zero_order_pos
#print axioms lemma55_actual_zeta_local_multiplicity_eq_count
#print axioms lemma55_actual_zeta_local_multiplicity_bound
#print axioms lemma55_actual_zeta_normalized_odd_power_error_bound
#print axioms lemma55_actual_zeta_weighted_power_error_uniform_bound
#print axioms lemma55_actual_zeta_weighted_real_power_error_uniform_bound
#print axioms lemma55_actual_zeta_weighted_pole_correction
#print axioms lemma55_actual_zeta_zero_factor_eq_product
#print axioms lemma55_actual_zeta_zero_factor_center_bound
#print axioms lemma55_actual_zeta_zero_factor_outer_lower_bound
#print axioms lemma55_actual_zeta_zero_factor_outer_ne_zero
#print axioms lemma55_actual_zeta_removed_meromorphic_order
#print axioms lemma55_actual_zeta_zero_factor_analytic
#print axioms lemma55_actual_zeta_zero_factor_order
#print axioms lemma55_actual_zeta_zero_removed_order
#print axioms lemma55_actual_zeta_zero_removed_analytic
#print axioms lemma55_actual_zeta_zero_removed_ne_zero
#print axioms lemma55_actual_zeta_zero_removed_eq_quotient
#print axioms lemma55_actual_zeta_zero_factorization
#print axioms lemma55_actual_zeta_local_zero_higher_derivative
#print axioms lemma55_actual_zeta_power_sum_remainder_norm_eq
#print axioms lemma55_actual_zeta_power_sum_remainder_bound
#print axioms lemma55_actual_zeta_power_sum_remainder_sum_bound
#print axioms lemma55_actual_zeta_normalized_pole_correction
#print axioms lemma55_actual_zeta_zero_power_sum_eq
#print axioms lemma55_actual_zeta_pole_corrected_power_error_bound
#print axioms lemma55_actual_zeta_zero_removed_outer_bound
#print axioms lemma55_actual_zeta_zero_removed_closed_disk_bound
#print axioms lemma55_actual_zeta_zero_removed_center_lower_bound
#print axioms lemma55_zeta_zero_removed_ratio_bound_gt_one
#print axioms lemma55_actual_zeta_zero_removed_ratio_bound
#print axioms lemma55_actual_zeta_zero_removed_log_ratio_bound
#print axioms lemma55_actual_zeta_zero_removed_log_exists
#print axioms lemma55_actual_zeta_zero_removed_log_hasDerivAt
#print axioms lemma55_actual_zeta_zero_removed_log_closed_bound
#print axioms lemma55_actual_zeta_zero_removed_log_cauchy_bound
