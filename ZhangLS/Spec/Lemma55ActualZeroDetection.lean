import ZhangLS.Spec.Lemma55FejerDetection
import ZhangLS.Spec.Lemma55ZeroPowerDerivatives
import ZhangLS.Spec.Lemma55OriginalRegionZeros
import Mathlib.Data.Finset.Max

/-!
# Fejér detection of actual local zeros, with optional zero removal

Every nonempty subset of the actual local zero set has a largest inverse
square. Its normalization lies in the closed unit disk and its actual
multiplicity is positive. The finite detection lower bound therefore
applies to actual zero power sums, also after removing one chosen zero.
-/

namespace ZhangLS.Spec

open Complex Metric Set Finset

noncomputable def lemma55ZeroInverseSquare (t : ℝ) (ρ : ℂ) : ℂ :=
  (lemma55JensenCenter t - ρ)⁻¹ ^ 2

theorem lemma55_actual_local_zero_center_distance
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma55LocalZeroFinset χ t) :
    1 < ‖lemma55JensenCenter t - ρ‖ := by
  have hr := lemma55_actual_zero_re_lt_one χ hD
    ((lemma55_mem_actual_local_zero_finset χ hD t ρ).mp hρ).2
  have hn := re_le_norm (lemma55JensenCenter t - ρ)
  rw [sub_re, lemma55_jensen_center_re] at hn
  linarith only [hr, hn]

theorem lemma55_actual_inverse_square_norm_bounds
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma55LocalZeroFinset χ t) :
    0 < ‖lemma55ZeroInverseSquare t ρ‖ ∧ ‖lemma55ZeroInverseSquare t ρ‖ < 1 := by
  have hd := lemma55_actual_local_zero_center_distance χ hD hρ
  have hdpos : 0 < ‖lemma55JensenCenter t - ρ‖ := by linarith only [hd]
  have hi : 0 < ‖lemma55JensenCenter t - ρ‖⁻¹ := inv_pos.mpr hdpos
  have hi1 : ‖lemma55JensenCenter t - ρ‖⁻¹ < 1 :=
    (inv_lt_one₀ hdpos).mpr hd
  unfold lemma55ZeroInverseSquare
  rw [norm_pow, norm_inv]
  exact ⟨by positivity, by nlinarith only [hi, hi1]⟩

theorem lemma55_actual_subset_max_inverse_square
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (S : Finset ℂ)
    (hS : S ⊆ lemma55LocalZeroFinset χ t) (hne : S.Nonempty) :
    ∃ ρ₀ ∈ S, 0 < ‖lemma55ZeroInverseSquare t ρ₀‖ ∧
      ‖lemma55ZeroInverseSquare t ρ₀‖ < 1 ∧
      ∀ ρ ∈ S, ‖lemma55ZeroInverseSquare t ρ‖ ≤ ‖lemma55ZeroInverseSquare t ρ₀‖ := by
  obtain ⟨ρ₀, hρ₀, hmax⟩ := S.exists_max_image (fun ρ => ‖lemma55ZeroInverseSquare t ρ‖) hne
  have hb := lemma55_actual_inverse_square_norm_bounds χ hD (hS hρ₀)
  exact ⟨ρ₀, hρ₀, hb.1, hb.2, hmax⟩

lemma lemma55_normalized_inverse_square_unit (t : ℝ) (ρ₀ : ℂ)
    (hr : 0 < ‖lemma55ZeroInverseSquare t ρ₀‖) :
    ‖lemma55ZeroInverseSquare t ρ₀ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ)‖ = 1 := by
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']

lemma lemma55_normalized_inverse_square_le_one (t : ℝ) (ρ ρ₀ : ℂ)
    (hr : 0 < ‖lemma55ZeroInverseSquare t ρ₀‖)
    (hmax : ‖lemma55ZeroInverseSquare t ρ‖ ≤ ‖lemma55ZeroInverseSquare t ρ₀‖) :
    ‖lemma55ZeroInverseSquare t ρ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ)‖ ≤ 1 := by
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  simpa only [one_mul] using hmax

noncomputable def lemma55SubsetZeroPowerSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) (S : Finset ℂ) (k : ℕ) : ℂ :=
  ∑ ρ ∈ S, (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) /
    (lemma55JensenCenter t - ρ) ^ k

lemma lemma55_normalized_inverse_square_power_sum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) (S : Finset ℂ) (r : ℝ) (k : ℕ) :
    (∑ ρ ∈ S, (analyticOrderNatAt (dirichletLFunction χ) ρ : ℝ) *
      ((lemma55ZeroInverseSquare t ρ / (r : ℂ)) ^ k).re) =
        (lemma55SubsetZeroPowerSum χ t S (2 * k) / (r : ℂ) ^ k).re := by
  unfold lemma55SubsetZeroPowerSum lemma55ZeroInverseSquare
  rw [sum_div, Complex.re_sum]
  apply sum_congr rfl
  intro ρ _
  rw [div_pow, ← pow_mul, inv_pow]
  have he : ((analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) /
      (lemma55JensenCenter t - ρ) ^ (2 * k)) / (r : ℂ) ^ k =
        (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) *
          (((lemma55JensenCenter t - ρ) ^ (2 * k))⁻¹ / (r : ℂ) ^ k) := by ring
  rw [he]
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]

theorem lemma55_actual_subset_weighted_power_detection
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (S : Finset ℂ)
    (hS : S ⊆ lemma55LocalZeroFinset χ t) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ S)
    (hmax : ∀ ρ ∈ S, ‖lemma55ZeroInverseSquare t ρ‖ ≤ ‖lemma55ZeroInverseSquare t ρ₀‖)
    (J : ℕ) :
    (J : ℝ) / 4 - ∑ ρ ∈ S, (analyticOrderNatAt (dirichletLFunction χ) ρ : ℝ) ≤
      ∑ j ∈ range J,
        lemma55FejerDetectionWeight
          (lemma55ZeroInverseSquare t ρ₀ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ))⁻¹ J j *
          (lemma55SubsetZeroPowerSum χ t S (2 * (j + 1)) /
            (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ) ^ (j + 1)).re := by
  have hr := (lemma55_actual_inverse_square_norm_bounds χ hD (hS hρ₀)).1
  have hm : 1 ≤ (analyticOrderNatAt (dirichletLFunction χ) ρ₀ : ℝ) := by
    exact_mod_cast lemma55_actual_local_zero_order_pos χ hD (hS hρ₀)
  have h := lemma55_fejer_finite_weighted_power_detection S
    (fun ρ => (analyticOrderNatAt (dirichletLFunction χ) ρ : ℝ))
    (fun ρ => lemma55ZeroInverseSquare t ρ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ))
    hρ₀ (fun _ _ => Nat.cast_nonneg _) hm
    (fun ρ hρ => lemma55_normalized_inverse_square_le_one t ρ ρ₀ hr (hmax ρ hρ))
    (lemma55_normalized_inverse_square_unit t ρ₀ hr) J
  simpa only [lemma55_normalized_inverse_square_power_sum] using h

theorem lemma55_actual_subset_weighted_detection_log_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (S : Finset ℂ)
    (hS : S ⊆ lemma55LocalZeroFinset χ t) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ S)
    (hmax : ∀ ρ ∈ S, ‖lemma55ZeroInverseSquare t ρ‖ ≤ ‖lemma55ZeroInverseSquare t ρ₀‖)
    (J : ℕ) :
    (J : ℝ) / 4 - 13 * Real.log (D : ℝ) ≤
      ∑ j ∈ range J,
        lemma55FejerDetectionWeight
          (lemma55ZeroInverseSquare t ρ₀ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ))⁻¹ J j *
          (lemma55SubsetZeroPowerSum χ t S (2 * (j + 1)) /
            (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ) ^ (j + 1)).re := by
  have hN : ∑ ρ ∈ S, (analyticOrderNatAt (dirichletLFunction χ) ρ : ℝ) ≤
      13 * Real.log (D : ℝ) := by
    calc
      _ ≤ ∑ ρ ∈ lemma55LocalZeroFinset χ t,
          (analyticOrderNatAt (dirichletLFunction χ) ρ : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.cast_nonneg _)
      _ = (lemma55LocalMultiplicity χ t : ℝ) := by simp [lemma55LocalMultiplicity]
      _ ≤ _ := lemma55_actual_local_multiplicity_bound χ hD hL ht
  have hd := lemma55_actual_subset_weighted_power_detection χ hD t S hS hρ₀ hmax J
  linarith only [hN, hd]

end ZhangLS.Spec
