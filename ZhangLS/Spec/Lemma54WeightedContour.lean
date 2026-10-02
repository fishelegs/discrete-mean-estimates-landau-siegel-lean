import ZhangLS.Spec.Lemma54WeightedContourEstimates

/-! # Limiting weighted contours and both actual derivative tails -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma54_gaussian_linear_tendsto_zero {B : ℝ} (hB : 0 < B) (q d : ℝ) :
    Tendsto (fun R : ℝ => Real.exp (d + q * R - B ^ 2 * R ^ 2)) atTop (𝓝 0) := by
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hlin : Tendsto (fun R : ℝ => B ^ 2 * R - q) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_const_mul_atTop_of_pos hBsq).mpr tendsto_id)
  have hquad := Tendsto.atTop_mul_atTop₀ hlin tendsto_id
  have hq : Tendsto (fun R : ℝ => (B ^ 2 * R - q) * R - d) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hquad
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq)
  convert he using 1
  ext R
  dsimp only [Function.comp_apply]
  congr 1
  ring

theorem lemma54_weighted_majorant_tendsto_zero {D : ℕ} (hB : 0 < lemma53PaperScale D) :
    Tendsto (lemma54WeightedMajorant D) atTop (𝓝 0) := by
  have h := ((lemma54_gaussian_linear_tendsto_zero hB (5 / 2) 0).add
    (lemma54_gaussian_linear_tendsto_zero hB (1 / 2) 0)).const_mul lemma54WeightedConstant
  simpa only [lemma54WeightedMajorant, zero_add, mul_zero, add_zero] using h

theorem lemma54_weighted_right_vertical_tendsto_zero {D : ℕ}
    (hB : 1 ≤ lemma53PaperScale D) {n : ℕ} (hn : n ≤ 2)
    {x : ℝ} (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) :
    Tendsto (fun R : ℝ => ∫ v : ℝ in 0..lemma53LargeHeight D,
      lemma54WeightedKernel D x n ((R : ℂ) + (v : ℂ) * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg := (lemma54_weighted_majorant_tendsto_zero
    (by linarith : 0 < lemma53PaperScale D)).const_mul (Real.exp 1 / lemma53PaperScale D)
  simp only [mul_zero] at hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun R => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (lemma53LargeEndpoint x)] with R hR
  exact lemma54_weighted_vertical_bound hB hn hx hX ht hR

theorem lemma54_weighted_infinite_contour_shift {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) {n : ℕ} (hn : n ≤ 2) {x : ℝ} (hx : 0 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D) :
    (∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma54WeightedKernel D x n (u : ℂ)) =
      (∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma54WeightedKernel D x n
        ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)) +
      I * (∫ v : ℝ in 0..lemma53LargeHeight D, lemma54WeightedKernel D x n
        ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)) := by
  have hr := intervalIntegral_tendsto_integral_Ioi (lemma53LargeEndpoint x)
    (lemma54_weighted_kernel_integrable hD hn x).integrableOn tendsto_id
  have hs := intervalIntegral_tendsto_integral_Ioi (lemma53LargeEndpoint x)
    (lemma54_weighted_ray_integrable hD hB hn hx hX ht) tendsto_id
  have hv := lemma54_weighted_right_vertical_tendsto_zero hB hn hx hX ht
  have hc := (hs.add_const (I * (∫ v : ℝ in 0..lemma53LargeHeight D,
    lemma54WeightedKernel D x n ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)))).sub
    (hv.const_mul I)
  simp only [mul_zero, sub_zero] at hc
  apply tendsto_nhds_unique hr
  apply hc.congr'
  exact Eventually.of_forall fun R =>
    (lemma53_entire_rectangle_shift _ (lemma54_weighted_kernel_differentiable D x n)
      (lemma53LargeEndpoint x) R (lemma53LargeHeight D)).symm

noncomputable def lemma54DerivativeTail (D : ℕ) (x : ℝ) : ℝ :=
  lemma54WeightedConstant * (4 + 2 * Real.exp 1) *
      Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) +
    2 * lemma54WeightedConstant * Real.sqrt Real.pi * Real.exp 3 *
      Real.exp (-(x ^ (99 / 100 : ℝ)) / lemma53PaperScale D)

theorem lemma54_weighted_large_range_estimate {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {n : ℕ} (hn : n ≤ 2) {x : ℝ} (hx : 0 < x)
    (hxhi : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    ‖∫ u : ℝ, lemma54WeightedKernel D x n (u : ℂ)‖ ≤ lemma54DerivativeTail D x := by
  obtain ⟨hx1, hX, hB⟩ := lemma53_large_range_parameters hL hxhi
  have ht : 0 ≤ lemma51PaperT0 D := by
    unfold lemma51PaperT0
    have hL0 : 0 ≤ lemma23PaperL D := by linarith
    positivity
  have hi := lemma54_weighted_kernel_integrable hD hn x
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := lemma53LargeEndpoint x)
    hi.integrableOn hi.integrableOn
  rw [lemma54_weighted_infinite_contour_shift hD hB hn hx hX.le ht] at hsplit
  rw [← hsplit]
  have hn1 := norm_add_le
    (∫ u : ℝ in Iic (lemma53LargeEndpoint x), lemma54WeightedKernel D x n (u : ℂ))
    ((∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma54WeightedKernel D x n
      ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)) +
      I * (∫ v : ℝ in 0..lemma53LargeHeight D, lemma54WeightedKernel D x n
        ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)))
  have hn2 := norm_add_le
    (∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma54WeightedKernel D x n
      ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I))
    (I * (∫ v : ℝ in 0..lemma53LargeHeight D, lemma54WeightedKernel D x n
      ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)))
  rw [norm_mul, norm_I, one_mul] at hn2
  have hleft := lemma54_weighted_left_tail_bound (D := D) hn hx1.le
  have hvert := lemma54_weighted_left_vertical_bound hB hn hx1 hX.le ht
  have hright := lemma54_weighted_right_ray_bound hD hB hn hx hX.le ht
  dsimp only [lemma53LargePower] at hright
  unfold lemma54DerivativeTail
  nlinarith only [hn1, hn2, hleft, hvert, hright]

theorem lemma54_actual_first_deriv_large_range {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x)
    (hxhi : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    ‖deriv (lemma53PaperDelta D) x‖ ≤ lemma54DerivativeTail D x := by
  rw [lemma54_actual_delta_deriv hD hx]
  unfold lemma54FirstIntegral
  simpa only [lemma54_weighted_kernel_one_real] using
    lemma54_weighted_large_range_estimate hD hL (n := 1) (by norm_num) hx hxhi

theorem lemma54_actual_second_deriv_large_range {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x)
    (hxhi : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    ‖deriv (deriv (lemma53PaperDelta D)) x‖ ≤ lemma54DerivativeTail D x := by
  rw [lemma54_actual_delta_second_deriv hD hx]
  unfold lemma54SecondIntegral
  simpa only [lemma54_weighted_kernel_two_real] using
    lemma54_weighted_large_range_estimate hD hL (n := 2) (by norm_num) hx hxhi

end ZhangLS.Spec
