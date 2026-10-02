import ZhangLS.Spec.Lemma55FejerKernel
import Mathlib.Data.Complex.BigOperators

/-!
# Finite weighted detection for local zero power sums

Rotating a unit term to one gives a lower bound J/4 minus the total
weight. The same expression uses nonnegative power coefficients at
most two, so summable analytic errors can later be absorbed uniformly.
-/

namespace ZhangLS.Spec

open Complex Finset

noncomputable def lemma55FejerWeight (J j : ℕ) : ℝ :=
  ((J - j : ℕ) : ℝ) / ((J + 1 : ℕ) : ℝ)

lemma lemma55_fejer_weight_nonneg (J j : ℕ) : 0 ≤ lemma55FejerWeight J j := by
  unfold lemma55FejerWeight
  positivity

lemma lemma55_fejer_weight_le_one (J j : ℕ) : lemma55FejerWeight J j ≤ 1 := by
  unfold lemma55FejerWeight
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (J + 1 : ℕ))).mpr
  have h : J - j ≤ J + 1 := by omega
  simpa only [one_mul] using (show ((J - j : ℕ) : ℝ) ≤ ((J + 1 : ℕ) : ℝ) by exact_mod_cast h)

lemma lemma55_fejer_kernel_eq_weighted (z : ℂ) (J : ℕ) :
    lemma55FejerKernel z J =
      ∑ j ∈ range J, lemma55FejerWeight J j * (z ^ (j + 1)).re := by
  unfold lemma55FejerKernel lemma55FejerWeight
  have h := congrArg Complex.re (lemma55_fejer_nested_eq_weighted z J)
  simp only [Complex.re_sum, mul_re, natCast_re, natCast_im, zero_mul, sub_zero] at h
  simp only [mul_re] at ⊢
  rw [h, sum_div]
  apply sum_congr rfl
  intro j _
  ring

noncomputable def lemma55FejerDetector (z v : ℂ) (J : ℕ) : ℝ :=
  lemma55FejerKernel z J + (1 / 2 : ℝ) * lemma55FejerKernel (z * v) J +
    (1 / 2 : ℝ) * lemma55FejerKernel (z * star v) J

lemma lemma55_fejer_detector_lower_bound {z v : ℂ}
    (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) (J : ℕ) :
    -1 ≤ lemma55FejerDetector z v J := by
  have hprod : ‖z * v‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith only [hz, hv, norm_nonneg z, norm_nonneg v]
  have hstar : ‖z * star v‖ ≤ 1 := by simpa only [norm_mul, norm_star] using hprod
  have h₁ := lemma55_fejer_kernel_lower_bound hz J
  have h₂ := lemma55_fejer_kernel_lower_bound hprod J
  have h₃ := lemma55_fejer_kernel_lower_bound hstar J
  unfold lemma55FejerDetector
  linarith only [h₁, h₂, h₃]

lemma lemma55_fejer_detector_at_unit {z : ℂ} (hz : ‖z‖ = 1) (J : ℕ) :
    (J : ℝ) / 4 - 1 ≤ lemma55FejerDetector z z⁻¹ J := by
  have hzne : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hv : ‖z⁻¹‖ ≤ 1 := by simp [norm_inv, hz]
  have hc : ‖z * star z⁻¹‖ ≤ 1 := by simp [hz]
  have h₁ := lemma55_fejer_kernel_lower_bound hz.le J
  have h₃ := lemma55_fejer_kernel_lower_bound hc J
  unfold lemma55FejerDetector
  rw [mul_inv_cancel₀ hzne, lemma55_fejer_kernel_at_one]
  linarith only [h₁, h₃]

noncomputable def lemma55FejerDetectionWeight (v : ℂ) (J j : ℕ) : ℝ :=
  lemma55FejerWeight J j * (1 + (v ^ (j + 1)).re)

lemma lemma55_fejer_detector_eq_weighted (z v : ℂ) (J : ℕ) :
    lemma55FejerDetector z v J =
      ∑ j ∈ range J, lemma55FejerDetectionWeight v J j * (z ^ (j + 1)).re := by
  unfold lemma55FejerDetector lemma55FejerDetectionWeight
  simp only [lemma55_fejer_kernel_eq_weighted, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [mul_pow, mul_pow, ← star_pow]
  simp only [mul_re, star_def, conj_re, conj_im]
  ring

lemma lemma55_fejer_detection_weight_bounds {v : ℂ} (hv : ‖v‖ ≤ 1) (J j : ℕ) :
    0 ≤ lemma55FejerDetectionWeight v J j ∧ lemma55FejerDetectionWeight v J j ≤ 2 := by
  have hp : ‖v ^ (j + 1)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg v) hv
  have hre : |(v ^ (j + 1)).re| ≤ 1 := (abs_re_le_norm _).trans hp
  have hf := lemma55_fejer_weight_nonneg J j
  have hf1 := lemma55_fejer_weight_le_one J j
  unfold lemma55FejerDetectionWeight
  constructor
  · exact mul_nonneg hf (by linarith only [(abs_le.mp hre).1])
  · nlinarith only [hf, hf1, (abs_le.mp hre).1, (abs_le.mp hre).2]

theorem lemma55_fejer_finite_detection {ι : Type*} (S : Finset ι)
    (m : ι → ℝ) (z : ι → ℂ) {i₀ : ι}
    (hi₀ : i₀ ∈ S) (hm : ∀ i ∈ S, 0 ≤ m i) (hm₀ : 1 ≤ m i₀)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (hz₀ : ‖z i₀‖ = 1) (J : ℕ) :
    (J : ℝ) / 4 - ∑ i ∈ S, m i ≤
      ∑ i ∈ S, m i * lemma55FejerDetector (z i) (z i₀)⁻¹ J := by
  have hv : ‖(z i₀)⁻¹‖ ≤ 1 := by simp [norm_inv, hz₀]
  have hpos : ∀ i ∈ S,
      0 ≤ m i * (lemma55FejerDetector (z i) (z i₀)⁻¹ J + 1) := by
    intro i hi
    exact mul_nonneg (hm i hi)
      (by linarith only [lemma55_fejer_detector_lower_bound (hz i hi) hv J])
  have hspecial := lemma55_fejer_detector_at_unit hz₀ J
  have hJ : 0 ≤ (J : ℝ) / 4 := by positivity
  have hs : (J : ℝ) / 4 ≤ m i₀ * (lemma55FejerDetector (z i₀) (z i₀)⁻¹ J + 1) := by
    nlinarith only [hspecial, hm₀, hJ]
  have hsum := Finset.single_le_sum hpos hi₀
  have htotal := hs.trans hsum
  simp only [mul_add, mul_one, sum_add_distrib] at htotal
  linarith only [htotal]

theorem lemma55_fejer_finite_weighted_power_detection {ι : Type*} (S : Finset ι)
    (m : ι → ℝ) (z : ι → ℂ) {i₀ : ι}
    (hi₀ : i₀ ∈ S) (hm : ∀ i ∈ S, 0 ≤ m i) (hm₀ : 1 ≤ m i₀)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (hz₀ : ‖z i₀‖ = 1) (J : ℕ) :
    (J : ℝ) / 4 - ∑ i ∈ S, m i ≤
      ∑ j ∈ range J, lemma55FejerDetectionWeight (z i₀)⁻¹ J j *
        (∑ i ∈ S, m i * (z i ^ (j + 1)).re) := by
  have h := lemma55_fejer_finite_detection S m z hi₀ hm hm₀ hz hz₀ J
  apply h.trans_eq
  simp only [lemma55_fejer_detector_eq_weighted, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

end ZhangLS.Spec
