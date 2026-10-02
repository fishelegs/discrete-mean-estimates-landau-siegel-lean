import ZhangLS.Spec.Lemma55ZeroNormalization

/-!
# Actual weighted even-power error budget

The Fejér coefficients lie in [0,2]. Distinct odd derivative orders
correspond to the even zero powers used by the detector. Combining the
actual all-order remainder sum with the candidate normalization gives
an exponential-cost bound and the stronger J-independent bound 79200 log D.
The latter retains the actual geometric decay after normalization.
-/

namespace ZhangLS.Spec

open Complex Finset

theorem lemma55_actual_odd_power_remainder_sum_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (J : ℕ) :
    (∑ j ∈ range J,
      ‖lemma55NormalizedLogDerivative χ t (2 * j + 1) -
        lemma55LocalZeroPowerSum χ t (2 * (j + 1))‖) ≤ 71280 * Real.log (D : ℝ) := by
  have hi : Set.InjOn (fun j : ℕ => 2 * j + 1) (range J) := by
    intro a _ b _ h
    dsimp only at h
    omega
  have h := lemma55_actual_power_sum_remainder_sum_bound χ hD hL ht
    ((range J).image (fun j : ℕ => 2 * j + 1))
  rw [sum_image hi] at h
  simpa only [show ∀ j : ℕ, 2 * j + 1 + 1 = 2 * (j + 1) by intro j; omega] using h

noncomputable def lemma55WeightedZeroPowerSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t r : ℝ) (v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    lemma55LocalZeroPowerSum χ t (2 * (j + 1)) / (r : ℂ) ^ (j + 1)

noncomputable def lemma55WeightedLogDerivative {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t r : ℝ) (v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    lemma55NormalizedLogDerivative χ t (2 * j + 1) / (r : ℂ) ^ (j + 1)

lemma lemma55_weighted_complex_difference_bound {w r B : ℝ} {a b : ℂ} (k : ℕ)
    (hw : 0 ≤ w) (hw2 : w ≤ 2) (hr : 0 < r) (hB : 0 ≤ B) (hk : r⁻¹ ^ k ≤ B) :
    ‖(w : ℂ) * a / (r : ℂ) ^ k - (w : ℂ) * b / (r : ℂ) ^ k‖ ≤
      2 * B * ‖a - b‖ := by
  rw [← sub_div, ← mul_sub, norm_div, norm_mul, norm_pow,
    norm_real, Real.norm_eq_abs, abs_of_nonneg hw,
    norm_real, Real.norm_eq_abs, abs_of_pos hr, div_eq_mul_inv, ← inv_pow]
  have he : w * ‖a - b‖ * r⁻¹ ^ k = (w * r⁻¹ ^ k) * ‖a - b‖ := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    w * r⁻¹ ^ k ≤ w * B := mul_le_mul_of_nonneg_left hk hw
    _ ≤ 2 * B := mul_le_mul_of_nonneg_right hw2 hB

theorem lemma55_actual_weighted_power_error_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedLogDerivative χ t r v J - lemma55WeightedZeroPowerSum χ t r v J‖ ≤
      142560 * Real.log (D : ℝ) * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ)) := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  unfold lemma55WeightedLogDerivative lemma55WeightedZeroPowerSum
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range J,
        ‖(lemma55FejerDetectionWeight v J j : ℂ) * lemma55NormalizedLogDerivative χ t (2 * j + 1) /
            (r : ℂ) ^ (j + 1) -
          (lemma55FejerDetectionWeight v J j : ℂ) * lemma55LocalZeroPowerSum χ t (2 * (j + 1)) /
            (r : ℂ) ^ (j + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range J,
        2 * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ)) *
          ‖lemma55NormalizedLogDerivative χ t (2 * j + 1) -
            lemma55LocalZeroPowerSum χ t (2 * (j + 1))‖ := by
      apply sum_le_sum
      intro j hj
      have hw := lemma55_fejer_detection_weight_bounds hv J j
      exact lemma55_weighted_complex_difference_bound (j + 1) hw.1 hw.2 hr
        (Real.exp_nonneg _) (lemma55_normalization_first_powers_exp_bound hLp hr hlower J j hj)
    _ = (2 * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ))) *
        ∑ j ∈ range J, ‖lemma55NormalizedLogDerivative χ t (2 * j + 1) -
          lemma55LocalZeroPowerSum χ t (2 * (j + 1))‖ := by rw [mul_sum]
    _ ≤ (2 * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ))) *
        (71280 * Real.log (D : ℝ)) := mul_le_mul_of_nonneg_left
      (lemma55_actual_odd_power_remainder_sum_bound χ hD hL ht J) (by positivity)
    _ = _ := by ring

theorem lemma55_actual_weighted_real_power_error_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    |(lemma55WeightedLogDerivative χ t r v J).re -
      (lemma55WeightedZeroPowerSum χ t r v J).re| ≤
      142560 * Real.log (D : ℝ) * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ)) := by
  have h := abs_re_le_norm (lemma55WeightedLogDerivative χ t r v J -
    lemma55WeightedZeroPowerSum χ t r v J)
  rw [sub_re] at h
  exact h.trans (lemma55_actual_weighted_power_error_bound χ hD hL ht hr hlower hv J)

lemma lemma55_normalized_remainder_geometric_ratio {L r : ℝ}
    (hL : 2000 ≤ L) (hr : 0 < r) (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r) :
    (64 / 81 : ℝ) * r⁻¹ ≤ 4 / 5 := by
  have hLp : 0 < L := by linarith only [hL]
  have ha : 0 < 1 + 2 / L := by positivity
  have hi : r⁻¹ ≤ (1 + 2 / L) ^ 2 := by
    have h := (inv_le_inv₀ hr (by positivity : 0 < ((1 + 2 / L)⁻¹) ^ 2)).mpr hlower
    simpa only [← inv_pow, inv_inv] using h
  have hd : 2 / L ≤ (1 : ℝ) / 1000 := by
    apply (div_le_iff₀ hLp).mpr
    linarith only [hL]
  have ha1 : 1 + 2 / L ≤ (1001 / 1000 : ℝ) := by linarith only [hd]
  have hp := pow_le_pow_left₀ ha.le ha1 2
  calc
    _ ≤ (64 / 81 : ℝ) * (1 + 2 / L) ^ 2 := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ ≤ (64 / 81 : ℝ) * (1001 / 1000 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ _ := by norm_num

theorem lemma55_actual_normalized_odd_power_error_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r) (j : ℕ) :
    ‖(lemma55NormalizedLogDerivative χ t (2 * j + 1) -
      lemma55LocalZeroPowerSum χ t (2 * (j + 1))) / (r : ℂ) ^ (j + 1)‖ ≤
        (1584 * Real.log (D : ℝ)) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j) := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hb := lemma55_actual_power_sum_remainder_bound χ hD hL ht (2 * j + 1)
  have hn : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [hn] at hb
  have hq := lemma55_normalized_remainder_geometric_ratio hL hr hlower
  rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hr,
    div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ (990 * (((2 * j + 1 : ℕ) : ℝ) + 1) * Real.log (D : ℝ) *
        (8 / 9 : ℝ) ^ (2 * (j + 1))) * r⁻¹ ^ (j + 1) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (1980 * ((j : ℝ) + 1) * Real.log (D : ℝ)) *
        ((64 / 81 : ℝ) * r⁻¹) ^ (j + 1) := by
      rw [pow_mul, mul_pow]
      push_cast
      norm_num only [show (8 / 9 : ℝ) ^ 2 = 64 / 81 by norm_num]
      ring
    _ ≤ (1980 * ((j : ℝ) + 1) * Real.log (D : ℝ)) * (4 / 5 : ℝ) ^ (j + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq (j + 1)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

lemma lemma55_successor_geometric_finite_bound (S : Finset ℕ) :
    (∑ j ∈ S, ((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j) ≤ 25 := by
  have hr : ‖(4 / 5 : ℝ)‖ < 1 := by norm_num
  have hs : HasSum (fun j : ℕ => ((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j) (25 : ℝ) := by
    convert (hasSum_coe_mul_geometric_of_norm_lt_one hr).add (hasSum_geometric_of_norm_lt_one hr) using 1
    · ext j
      ring
    · norm_num
  calc
    _ ≤ ∑' j : ℕ, ((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j :=
      hs.summable.sum_le_tsum S (fun j _ => by positivity)
    _ = _ := hs.tsum_eq

theorem lemma55_actual_weighted_power_error_uniform_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedLogDerivative χ t r v J - lemma55WeightedZeroPowerSum χ t r v J‖ ≤
      79200 * Real.log (D : ℝ) := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  unfold lemma55WeightedLogDerivative lemma55WeightedZeroPowerSum
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range J,
        ‖(lemma55FejerDetectionWeight v J j : ℂ) * lemma55NormalizedLogDerivative χ t (2 * j + 1) /
            (r : ℂ) ^ (j + 1) -
          (lemma55FejerDetectionWeight v J j : ℂ) * lemma55LocalZeroPowerSum χ t (2 * (j + 1)) /
            (r : ℂ) ^ (j + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range J, (3168 * Real.log (D : ℝ)) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j) := by
      apply sum_le_sum
      intro j _
      have hw := lemma55_fejer_detection_weight_bounds hv J j
      have he : (lemma55FejerDetectionWeight v J j : ℂ) * lemma55NormalizedLogDerivative χ t (2 * j + 1) /
          (r : ℂ) ^ (j + 1) -
        (lemma55FejerDetectionWeight v J j : ℂ) * lemma55LocalZeroPowerSum χ t (2 * (j + 1)) /
          (r : ℂ) ^ (j + 1) =
        (lemma55FejerDetectionWeight v J j : ℂ) *
          ((lemma55NormalizedLogDerivative χ t (2 * j + 1) -
            lemma55LocalZeroPowerSum χ t (2 * (j + 1))) / (r : ℂ) ^ (j + 1)) := by ring
      rw [he, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1]
      have hb := lemma55_actual_normalized_odd_power_error_bound χ hD hL ht hr hlower j
      calc
        _ ≤ 2 * ((1584 * Real.log (D : ℝ)) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j)) :=
          mul_le_mul hw.2 hb (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    _ = (3168 * Real.log (D : ℝ)) * ∑ j ∈ range J, ((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ (3168 * Real.log (D : ℝ)) * 25 := mul_le_mul_of_nonneg_left
      (lemma55_successor_geometric_finite_bound (range J)) (by positivity)
    _ = _ := by ring

theorem lemma55_actual_weighted_real_power_error_uniform_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    |(lemma55WeightedLogDerivative χ t r v J).re -
      (lemma55WeightedZeroPowerSum χ t r v J).re| ≤ 79200 * Real.log (D : ℝ) := by
  have h := abs_re_le_norm (lemma55WeightedLogDerivative χ t r v J -
    lemma55WeightedZeroPowerSum χ t r v J)
  rw [sub_re] at h
  exact h.trans (lemma55_actual_weighted_power_error_uniform_bound χ hD hL ht hr hlower hv J)

end ZhangLS.Spec
