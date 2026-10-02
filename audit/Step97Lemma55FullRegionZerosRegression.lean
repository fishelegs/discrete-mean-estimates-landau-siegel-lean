import ZhangLS.Spec.Lemma55OriginalRegionZeros

/-! Actual local multiplicities, both original height endpoints, and exact
membership in the original full region's zero set. This is a finite/count
regression, not a claim that the original region has only one zero. -/

open Complex Metric Set ZhangLS.Spec

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

example {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : 2 ≤ s.re) :
    (1 : ℝ) / 4 ≤ ‖(@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) s‖ :=
  lemma55_actual_L_norm_lower_bound χ hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {z : ℂ} (hz : z ∈ closedBall (2 + ((2 * (D : ℝ) : ℝ) : ℂ) * I) (3 / 2 : ℝ)) :
    ‖dirichletLFunction χ z‖ ≤ 8 * (D : ℝ) ^ 2 :=
  lemma55_actual_high_height_disk_bound χ hD (by simp) hz

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {z : ℂ} (hz : z ∈ closedBall (2 + ((-(2 * (D : ℝ)) : ℝ) : ℂ) * I) (3 / 2 : ℝ)) :
    ‖dirichletLFunction χ z‖ ≤ 8 * (D : ℝ) ^ 2 :=
  lemma55_actual_high_height_disk_bound χ hD (by simp) hz

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    ((∑ ρ ∈ lemma55LocalZeroFinset χ t,
      (analyticOrderNatAt (dirichletLFunction χ) ρ : ℤ)) : ℝ) ≤ 13 * Real.log (D : ℝ) := by
  have hcount := lemma55_actual_jensen_multiplicity_bound χ hD hL ht
  rw [lemma55_actual_multiplicity_count_eq_sum_orders χ hD t] at hcount
  simpa only [Int.cast_sum] using hcount

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (ρ : ℂ) :
    ρ ∈ lemma55LocalZeroFinset χ t ↔
      ρ ∈ closedBall (2 + (t : ℂ) * I) (5 / 4 : ℝ) ∧ dirichletLFunction χ ρ = 0 :=
  lemma55_mem_actual_local_zero_finset χ hD t ρ

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) :
    ∃ S : Finset ℂ,
      (∀ s : ℂ, s ∈ S ↔
        (1 - 2 / Real.log (D : ℝ) < s.re ∧ |s.im| < 2 * (D : ℝ)) ∧
          (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) s = 0) ∧
      (S.card : ℝ) ≤ 13 * (8 * (D : ℝ) + 1) * Real.log (D : ℝ) := by
  exact ⟨lemma55RegionZeroFinset χ, lemma55_mem_original_region_zero_finset χ hD hL,
    lemma55_original_region_zero_card_bound χ hD hL⟩

example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ) :
    ∃ ρₘ : ℂ, (1 - 2 / Real.log (D : ℝ) < ρₘ.re ∧ |ρₘ.im| < 2 * (D : ℝ)) ∧
      dirichletLFunction χ ρₘ = 0 ∧
      ∀ z : ℂ, (1 - 2 / Real.log (D : ℝ) < z.re ∧ |z.im| < 2 * (D : ℝ)) →
        dirichletLFunction χ z = 0 → z.re ≤ ρₘ.re :=
  lemma55_original_region_rightmost_zero_under_A χ hDN hA

#print axioms lemma55_hasSum_inverse_telescope
#print axioms lemma55_lseries_term_square_bound
#print axioms lemma55_actual_L_distance_to_one_bound
#print axioms lemma55_actual_L_norm_lower_bound
#print axioms lemma55_jensen_disk_re_lower_bound
#print axioms lemma55_actual_high_height_disk_bound
#print axioms lemma55_actual_L_analyticOnNhd
#print axioms lemma55_actual_jensen_center_lower_bound
#print axioms lemma55_actual_jensen_center_ne_zero
#print axioms lemma55_actual_jensen_multiplicity_bound
#print axioms lemma55_actual_analytic_order_finite
#print axioms lemma55_actual_local_divisor_eq_order
#print axioms lemma55_mem_actual_local_zero_finset
#print axioms lemma55_actual_local_zero_order_pos
#print axioms lemma55_actual_multiplicity_count_eq_sum_orders
#print axioms lemma55_actual_local_zero_card_bound
#print axioms lemma55_zero_grid_height_bound
#print axioms lemma55_zero_grid_index_bound
#print axioms lemma55_zero_grid_height_approximation
#print axioms lemma55_original_region_disk_cover
#print axioms lemma55_actual_zero_re_lt_one
#print axioms lemma55_mem_original_region_zero_finset
#print axioms lemma55_original_region_actual_zeros_finite
#print axioms lemma55_original_region_zero_card_bound
#print axioms lemma55_original_region_maximal_zero
#print axioms lemma55_original_region_contains_exceptional_zero
#print axioms lemma55_original_region_rightmost_zero_under_A
