import ZhangLS.Spec.Lemma53LargeContourEstimates

/-! # The limiting downward shift and complete original large-x estimate -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma53_gaussian_linear_tendsto_zero {B : ℝ} (hB : 0 < B) :
    Tendsto (fun R : ℝ => Real.exp (1 + R / 2 - B ^ 2 * R ^ 2)) atTop (𝓝 0) := by
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hlin : Tendsto (fun R : ℝ => B ^ 2 * R - 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_const_mul_atTop_of_pos hBsq).mpr tendsto_id)
  have hquad := Tendsto.atTop_mul_atTop₀ hlin tendsto_id
  have hq : Tendsto (fun R : ℝ => (B ^ 2 * R - 1 / 2) * R - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hquad
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq)
  convert he using 1
  ext R
  dsimp only [Function.comp_apply]
  congr 1
  ring

theorem lemma53_large_right_vertical_tendsto_zero {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {x : ℝ} (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) :
    Tendsto (fun R : ℝ => ∫ v : ℝ in 0..lemma53LargeHeight D,
      lemma53OscillatoryKernel D x ((R : ℂ) + (v : ℂ) * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg := (lemma53_gaussian_linear_tendsto_zero
    (by linarith : 0 < lemma53PaperScale D)).const_mul (1 / lemma53PaperScale D)
  simp only [mul_zero] at hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun R => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (lemma53LargeEndpoint x)] with R hR
  exact lemma53_large_vertical_bound hB hx hX ht hR

theorem lemma53_large_infinite_contour_shift {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) {x : ℝ} (hx : 0 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D) :
    (∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma53OscillatoryKernel D x (u : ℂ)) =
      (∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma53OscillatoryKernel D x
        ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)) +
      I * (∫ v : ℝ in 0..lemma53LargeHeight D, lemma53OscillatoryKernel D x
        ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)) := by
  have hr := intervalIntegral_tendsto_integral_Ioi (lemma53LargeEndpoint x)
    (lemma53_oscillatory_kernel_integrable hD x).integrableOn tendsto_id
  have hs := intervalIntegral_tendsto_integral_Ioi (lemma53LargeEndpoint x)
    (lemma53_large_ray_integrable hD hB hx hX ht) tendsto_id
  have hv := lemma53_large_right_vertical_tendsto_zero hB hx hX ht
  have hc := (hs.add_const (I * (∫ v : ℝ in 0..lemma53LargeHeight D,
    lemma53OscillatoryKernel D x ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)))).sub
    (hv.const_mul I)
  simp only [mul_zero, sub_zero] at hc
  apply tendsto_nhds_unique hr
  apply hc.congr'
  exact Eventually.of_forall fun R =>
    (lemma53_entire_rectangle_shift _ (lemma53_oscillatory_kernel_differentiable D x)
      (lemma53LargeEndpoint x) R (lemma53LargeHeight D)).symm

theorem lemma53_large_range_estimate {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x)
    (hxhi : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    ‖lemma53PaperDelta D x‖ ≤
      (2 + Real.exp 1) * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) +
        (Real.sqrt Real.pi * Real.exp 2) *
          Real.exp (-(x ^ (99 / 100 : ℝ)) / lemma53PaperScale D) := by
  obtain ⟨hx1, hX, hB⟩ := lemma53_large_range_parameters hL hxhi
  have ht : 0 ≤ lemma51PaperT0 D := by
    unfold lemma51PaperT0
    have hL0 : 0 ≤ lemma23PaperL D := by linarith
    positivity
  have hi := lemma53_oscillatory_kernel_integrable hD x
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := lemma53LargeEndpoint x)
    hi.integrableOn hi.integrableOn
  rw [lemma53_large_infinite_contour_shift hD hB hx hX.le ht] at hsplit
  rw [lemma53_mellin_oscillatory_identity hD hx]
  unfold lemma53OscillatoryDelta
  rw [← hsplit]
  have hn := (norm_add_le
    (∫ u : ℝ in Iic (lemma53LargeEndpoint x), lemma53OscillatoryKernel D x (u : ℂ))
    ((∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma53OscillatoryKernel D x
      ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)) +
       I * (∫ v : ℝ in 0..lemma53LargeHeight D, lemma53OscillatoryKernel D x
        ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I))))
  have hn2 := norm_add_le
    (∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma53OscillatoryKernel D x
      ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I))
    (I * (∫ v : ℝ in 0..lemma53LargeHeight D, lemma53OscillatoryKernel D x
      ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)))
  rw [norm_mul, norm_I, one_mul] at hn2
  have hleft := lemma53_large_left_tail_bound hD hx1.le
  have hvert := lemma53_large_left_vertical_bound hB hx1 hX.le ht
  have hright := lemma53_large_right_ray_bound hD hB hx hX.le ht
  dsimp only [lemma53LargePower] at hright
  nlinarith only [hn, hn2, hleft, hvert, hright]

end ZhangLS.Spec
