import ZhangLS.Spec.Lemma55HigherLogDerivative

/-! Actual L-function factorization at all points, nonzero removable
values at actual zeros, both height endpoints, and all-order actual
logarithmic-derivative errors. No full-region exclusion is asserted. -/

open Complex Metric Set ZhangLS.Spec

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (z : ℂ) :
    (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) z =
      (∏ ρ ∈ lemma55LocalZeroFinset χ t,
        (z - ρ) ^ analyticOrderNatAt (dirichletLFunction χ) ρ) * lemma55ZeroRemovedL χ t z := by
  rw [← lemma55_actual_zero_factor_eq_product χ hD t z]
  exact lemma55_actual_zero_factorization χ hD t z

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ lemma55LocalZeroFinset χ t) :
    lemma55ZeroRemovedL χ t ρ ≠ 0 :=
  lemma55_actual_zero_removed_ne_zero χ hD
    ((lemma55_mem_actual_local_zero_finset χ hD t ρ).mp hρ).1

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) :
    ‖deriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi)
        (lemma55JensenCenter (2 * (D : ℝ))) /
      (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi)
        (lemma55JensenCenter (2 * (D : ℝ))) -
        ∑ ρ ∈ lemma55LocalZeroFinset χ (2 * (D : ℝ)),
          (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) /
            (lemma55JensenCenter (2 * (D : ℝ)) - ρ)‖ ≤ 176 * Real.log (D : ℝ) :=
  lemma55_actual_center_local_logDeriv_error χ hD hL (by simp)

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi))
        (lemma55JensenCenter (-(2 * (D : ℝ)))) -
      iteratedDeriv n (lemma55LocalZeroLogDerivative χ (-(2 * (D : ℝ))))
        (lemma55JensenCenter (-(2 * (D : ℝ))))‖ / (n.factorial : ℝ) ≤
          990 * ((n : ℝ) + 1) * Real.log (D : ℝ) * (8 / 9 : ℝ) ^ (n + 1) :=
  lemma55_actual_normalized_logDeriv_remainder_bound χ hD hL (by simp) n

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (S : Finset ℕ) :
    (∑ n ∈ S,
      ‖iteratedDeriv n (logDeriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi))
          (lemma55JensenCenter t) -
        iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t)‖ /
          (n.factorial : ℝ)) ≤ 71280 * Real.log (D : ℝ) :=
  lemma55_actual_logDeriv_remainder_sum_bound χ hD hL ht S

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    ∃ ℓ : ℂ → ℂ, Lemma55ZeroRemovedLogData χ t ℓ ∧
      (∀ z ∈ closedBall (0 : ℂ) (9 / 8 : ℝ), ‖ℓ z‖ ≤ 990 * Real.log (D : ℝ)) ∧
      ∀ n : ℕ, ‖iteratedDeriv n ℓ 0‖ ≤
        n.factorial * (990 * Real.log (D : ℝ)) / (9 / 8 : ℝ) ^ n := by
  obtain ⟨ℓ, hℓ⟩ := lemma55_actual_zero_removed_log_exists χ hD t
  exact ⟨ℓ, hℓ, fun z hz => lemma55_actual_zero_removed_log_closed_bound χ hD hL ht hℓ hz,
    lemma55_actual_zero_removed_log_cauchy_bound χ hD hL ht hℓ⟩

#print axioms lemma55_actual_meromorphic_order_eq_nat
#print axioms lemma55_actual_zero_factor_analytic
#print axioms lemma55_actual_zero_factor_order
#print axioms lemma55_actual_zero_removed_order
#print axioms lemma55_actual_zero_removed_analytic
#print axioms lemma55_actual_zero_removed_ne_zero
#print axioms lemma55_actual_zero_removed_eq_quotient
#print axioms lemma55_actual_zero_factorization
#print axioms lemma55_actual_zero_factor_eq_product
#print axioms lemma55_actual_local_multiplicity_eq_count
#print axioms lemma55_actual_local_multiplicity_bound
#print axioms lemma55_actual_zero_factor_center_bound
#print axioms lemma55_actual_zero_factor_outer_lower_bound
#print axioms lemma55_actual_zero_factor_outer_ne_zero
#print axioms lemma55_actual_zero_removed_outer_bound
#print axioms lemma55_actual_zero_removed_closed_disk_bound
#print axioms lemma55_actual_zero_removed_center_lower_bound
#print axioms lemma55_zero_removed_ratio_bound_gt_one
#print axioms lemma55_actual_zero_removed_ratio_bound
#print axioms lemma55_actual_zero_removed_log_ratio_bound
#print axioms lemma55_actual_zero_removed_log_exists
#print axioms lemma55_actual_zero_removed_log_hasDerivAt
#print axioms lemma55_actual_zero_removed_log_closed_bound
#print axioms lemma55_actual_zero_removed_log_cauchy_bound
#print axioms lemma55_actual_zero_factor_logDeriv
#print axioms lemma55_actual_local_logDeriv_formula
#print axioms lemma55_actual_zero_removed_center_logDeriv_bound
#print axioms lemma55_actual_center_local_logDeriv_error
#print axioms lemma55_actual_zero_removed_higher_logDeriv_bound
#print axioms lemma55_actual_higher_logDeriv_remainder_eq
#print axioms lemma55_actual_higher_logDeriv_remainder_bound
#print axioms lemma55_actual_normalized_logDeriv_remainder_bound
#print axioms lemma55_actual_logDeriv_remainder_sum_bound
