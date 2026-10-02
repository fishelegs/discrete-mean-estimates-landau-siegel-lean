import ZhangLS.Spec.Lemma55ZetaZeroPowerDerivatives

/-! # Uniform normalized weighted error for actual zeta

The actual geometric decay persists after candidate normalization.
The full weighted error is at most 108000 log D for every detection
order J. The pole at one is included exactly, with actual zeta orders.
-/

namespace ZhangLS.Spec
open Complex Finset

noncomputable def lemma55ZetaWeightedZeroPowerSum (t r : ℝ) (v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    lemma55ZetaLocalZeroPowerSum t (2 * (j + 1)) / (r : ℂ) ^ (j + 1)

noncomputable def lemma55ZetaWeightedRemovedLogDerivative (t r : ℝ) (v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    lemma55ZetaNormalizedRemovedLogDerivative t (2 * j + 1) / (r : ℂ) ^ (j + 1)

theorem lemma55_actual_zeta_normalized_odd_power_error_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r) (j : ℕ) :
    ‖(lemma55ZetaNormalizedRemovedLogDerivative t (2 * j + 1) -
      lemma55ZetaLocalZeroPowerSum t (2 * (j + 1))) / (r : ℂ) ^ (j + 1)‖ ≤
        (2160 * Real.log (D : ℝ)) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j) := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hb := lemma55_actual_zeta_power_sum_remainder_bound hD hL ht (2 * j + 1)
  have hn : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [hn] at hb
  have hq := lemma55_normalized_remainder_geometric_ratio hL hr hlower
  rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hr,
    div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ (1350 * (((2 * j + 1 : ℕ) : ℝ) + 1) * Real.log (D : ℝ) *
        (8 / 9 : ℝ) ^ (2 * (j + 1))) * r⁻¹ ^ (j + 1) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2700 * ((j : ℝ) + 1) * Real.log (D : ℝ)) *
        ((64 / 81 : ℝ) * r⁻¹) ^ (j + 1) := by
      rw [pow_mul, mul_pow]
      push_cast
      norm_num only [show (8 / 9 : ℝ) ^ 2 = 64 / 81 by norm_num]
      ring
    _ ≤ (2700 * ((j : ℝ) + 1) * Real.log (D : ℝ)) * (4 / 5 : ℝ) ^ (j + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq (j + 1)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem lemma55_actual_zeta_weighted_power_error_uniform_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55ZetaWeightedRemovedLogDerivative t r v J - lemma55ZetaWeightedZeroPowerSum t r v J‖ ≤
      108000 * Real.log (D : ℝ) := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  unfold lemma55ZetaWeightedRemovedLogDerivative lemma55ZetaWeightedZeroPowerSum
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range J,
        ‖(lemma55FejerDetectionWeight v J j : ℂ) * lemma55ZetaNormalizedRemovedLogDerivative t (2 * j + 1) /
            (r : ℂ) ^ (j + 1) -
          (lemma55FejerDetectionWeight v J j : ℂ) * lemma55ZetaLocalZeroPowerSum t (2 * (j + 1)) /
            (r : ℂ) ^ (j + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range J, (4320 * Real.log (D : ℝ)) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j) := by
      apply sum_le_sum
      intro j _
      have hw := lemma55_fejer_detection_weight_bounds hv J j
      have he : (lemma55FejerDetectionWeight v J j : ℂ) * lemma55ZetaNormalizedRemovedLogDerivative t (2 * j + 1) /
          (r : ℂ) ^ (j + 1) -
        (lemma55FejerDetectionWeight v J j : ℂ) * lemma55ZetaLocalZeroPowerSum t (2 * (j + 1)) /
          (r : ℂ) ^ (j + 1) =
        (lemma55FejerDetectionWeight v J j : ℂ) *
          ((lemma55ZetaNormalizedRemovedLogDerivative t (2 * j + 1) -
            lemma55ZetaLocalZeroPowerSum t (2 * (j + 1))) / (r : ℂ) ^ (j + 1)) := by ring
      rw [he, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1]
      have hb := lemma55_actual_zeta_normalized_odd_power_error_bound hD hL ht hr hlower j
      calc
        _ ≤ 2 * ((2160 * Real.log (D : ℝ)) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j)) :=
          mul_le_mul hw.2 hb (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    _ = (4320 * Real.log (D : ℝ)) * ∑ j ∈ range J, ((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ (4320 * Real.log (D : ℝ)) * 25 := mul_le_mul_of_nonneg_left
      (lemma55_successor_geometric_finite_bound (range J)) (by positivity)
    _ = _ := by ring

theorem lemma55_actual_zeta_weighted_real_power_error_uniform_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    |(lemma55ZetaWeightedRemovedLogDerivative t r v J).re -
      (lemma55ZetaWeightedZeroPowerSum t r v J).re| ≤ 108000 * Real.log (D : ℝ) := by
  have h := abs_re_le_norm (lemma55ZetaWeightedRemovedLogDerivative t r v J -
    lemma55ZetaWeightedZeroPowerSum t r v J)
  rw [sub_re] at h
  exact h.trans (lemma55_actual_zeta_weighted_power_error_uniform_bound hD hL ht hr hlower hv J)


theorem lemma55_actual_zeta_weighted_pole_correction (t r : ℝ) (v : ℂ) (J : ℕ) :
    lemma55ZetaWeightedRemovedLogDerivative t r v J =
      ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55ZetaNormalizedLogDerivative t (2 * j + 1) +
          1 / (lemma55JensenCenter t - 1) ^ (2 * (j + 1))) / (r : ℂ) ^ (j + 1) := by
  unfold lemma55ZetaWeightedRemovedLogDerivative
  simp_rw [lemma55_actual_zeta_normalized_pole_correction]
  congr 1

end ZhangLS.Spec
