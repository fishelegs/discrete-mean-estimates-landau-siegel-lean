import ZhangLS.Spec.Lemma55WeightedPowerError

/-!
# Comparing the exceptional real zero with the pole at one

All centers have real part two. Inverse powers at a real β≤1 differ
from those at one by at most k(1−β). The actual Fejér coefficients and
normalization therefore give a finite weighted cancellation bound.
No positivity identity or full zero-exclusion conclusion is assumed.
-/

namespace ZhangLS.Spec

open Complex Finset

lemma lemma55_unit_disk_power_difference {a b : ℂ} {δ : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hδ : 0 ≤ δ) (hab : ‖a - b‖ ≤ δ) (k : ℕ) :
    ‖a ^ k - b ^ k‖ ≤ (k : ℝ) * δ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : a ^ (k + 1) - b ^ (k + 1) =
        a ^ k * (a - b) + (a ^ k - b ^ k) * b := by ring
    have hpow : ‖a ^ k‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg a) ha
    rw [he]
    calc
      _ ≤ ‖a ^ k * (a - b)‖ + ‖(a ^ k - b ^ k) * b‖ := norm_add_le _ _
      _ = ‖a ^ k‖ * ‖a - b‖ + ‖a ^ k - b ^ k‖ * ‖b‖ := by rw [norm_mul, norm_mul]
      _ ≤ δ + (k : ℝ) * δ := by
        have h₁ : ‖a ^ k‖ * ‖a - b‖ ≤ δ := by
          calc
            _ ≤ 1 * δ := mul_le_mul hpow hab (norm_nonneg _) (by norm_num)
            _ = δ := one_mul δ
        have h₂ : ‖a ^ k - b ^ k‖ * ‖b‖ ≤ (k : ℝ) * δ := by
          calc
            _ ≤ ((k : ℝ) * δ) * 1 := mul_le_mul ih hb (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
        linarith only [h₁, h₂]
      _ = ((k + 1 : ℕ) : ℝ) * δ := by push_cast; ring

lemma lemma55_real_pole_center_distance (t β : ℝ) (hβ : β ≤ 1) :
    1 ≤ ‖lemma55JensenCenter t - (β : ℂ)‖ := by
  have h := re_le_norm (lemma55JensenCenter t - (β : ℂ))
  rw [sub_re, lemma55_jensen_center_re, ofReal_re] at h
  linarith only [h, hβ]

theorem lemma55_real_pole_inverse_difference (t β : ℝ) (hβ : β ≤ 1) :
    ‖(lemma55JensenCenter t - 1)⁻¹ - (lemma55JensenCenter t - (β : ℂ))⁻¹‖ ≤ 1 - β := by
  have ha : 1 ≤ ‖lemma55JensenCenter t - 1‖ := by
    simpa only [ofReal_one] using lemma55_real_pole_center_distance t 1 le_rfl
  have hb := lemma55_real_pole_center_distance t β hβ
  have hap : 0 < ‖lemma55JensenCenter t - 1‖ := by linarith only [ha]
  have hbp : 0 < ‖lemma55JensenCenter t - (β : ℂ)‖ := by linarith only [hb]
  have hane : lemma55JensenCenter t - 1 ≠ 0 := norm_pos_iff.mp hap
  have hbne : lemma55JensenCenter t - (β : ℂ) ≠ 0 := norm_pos_iff.mp hbp
  have he : (lemma55JensenCenter t - 1)⁻¹ - (lemma55JensenCenter t - (β : ℂ))⁻¹ =
      ((1 - β : ℝ) : ℂ) /
        ((lemma55JensenCenter t - 1) * (lemma55JensenCenter t - (β : ℂ))) := by
    push_cast
    field_simp
    ring
  rw [he, norm_div, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hβ]), norm_mul]
  apply (div_le_iff₀ (mul_pos hap hbp)).mpr
  have hprod : 1 ≤ ‖lemma55JensenCenter t - 1‖ * ‖lemma55JensenCenter t - (β : ℂ)‖ := by
    simpa only [one_mul] using mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1)
      (norm_nonneg (lemma55JensenCenter t - 1))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hβ)

theorem lemma55_real_pole_inverse_power_difference (t β : ℝ) (hβ : β ≤ 1) (k : ℕ) :
    ‖(lemma55JensenCenter t - 1)⁻¹ ^ k - (lemma55JensenCenter t - (β : ℂ))⁻¹ ^ k‖ ≤
      (k : ℝ) * (1 - β) := by
  have hnorm (x : ℝ) (hx : x ≤ 1) : ‖(lemma55JensenCenter t - (x : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have hd := lemma55_real_pole_center_distance t x hx
    apply (inv_le_one₀ (by linarith only [hd] : 0 < ‖lemma55JensenCenter t - (x : ℂ)‖)).mpr hd
  exact lemma55_unit_disk_power_difference (by simpa using hnorm 1 le_rfl) (hnorm β hβ)
    (by linarith only [hβ]) (lemma55_real_pole_inverse_difference t β hβ) k

lemma lemma55_sum_successors (J : ℕ) :
    (∑ j ∈ range J, ((j : ℝ) + 1)) = (J : ℝ) * ((J : ℝ) + 1) / 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

noncomputable def lemma55WeightedExceptionalPoleDifference
    (t β r : ℝ) (v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    ((lemma55JensenCenter t - 1)⁻¹ ^ (2 * (j + 1)) -
      (lemma55JensenCenter t - (β : ℂ))⁻¹ ^ (2 * (j + 1))) / (r : ℂ) ^ (j + 1)

theorem lemma55_weighted_exceptional_pole_difference_bound
    (t β : ℝ) (hβ : β ≤ 1) {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r) {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedExceptionalPoleDifference t β r v J‖ ≤
      2 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / L) := by
  unfold lemma55WeightedExceptionalPoleDifference
  calc
    _ ≤ ∑ j ∈ range J,
        ‖(lemma55FejerDetectionWeight v J j : ℂ) *
          ((lemma55JensenCenter t - 1)⁻¹ ^ (2 * (j + 1)) -
            (lemma55JensenCenter t - (β : ℂ))⁻¹ ^ (2 * (j + 1))) / (r : ℂ) ^ (j + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ range J,
        (4 * (1 - β) * Real.exp (4 * (J : ℝ) / L)) * ((j : ℝ) + 1) := by
      apply sum_le_sum
      intro j hj
      have hw := lemma55_fejer_detection_weight_bounds hv J j
      have he := lemma55_weighted_complex_difference_bound (j + 1) hw.1 hw.2 hr
        (Real.exp_nonneg _) (lemma55_normalization_first_powers_exp_bound hL hr hlower J j hj)
        (a := (lemma55JensenCenter t - 1)⁻¹ ^ (2 * (j + 1)))
        (b := (lemma55JensenCenter t - (β : ℂ))⁻¹ ^ (2 * (j + 1)))
      have hpow := lemma55_real_pole_inverse_power_difference t β hβ (2 * (j + 1))
      have hscaled := mul_le_mul_of_nonneg_left hpow
        (by positivity : 0 ≤ 2 * Real.exp (4 * (J : ℝ) / L))
      rw [← sub_div, ← mul_sub] at he
      apply he.trans
      convert hscaled using 1
      push_cast
      ring
    _ = (4 * (1 - β) * Real.exp (4 * (J : ℝ) / L)) *
        ((J : ℝ) * ((J : ℝ) + 1) / 2) := by rw [← mul_sum, lemma55_sum_successors]
    _ = _ := by ring

end ZhangLS.Spec
