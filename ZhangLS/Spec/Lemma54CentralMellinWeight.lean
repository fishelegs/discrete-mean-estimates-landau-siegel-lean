import ZhangLS.Spec.Lemma54ActualGaussianConcentration

/-! # Quantitative Mellin-weight control on the original central window -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000

theorem lemma54_disk_window_weight_error {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {s : ℂ} (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D)
    {x : ℝ} (hx : x ∈ lemma54PaperWindow D) :
    ‖(x : ℂ) ^ (s - 1) - 1‖ ≤
      10400 * lemma44PaperAlpha D * Real.log (lemma23PaperL D) := by
  have hxb := lemma54_window_x_bounds hL hx
  have hlog := lemma54_window_log_bound hL hx
  have ha := (lemma54_disk_alpha_small hL).1
  have hz : ‖(Real.log x : ℂ) * (s - 1)‖ ≤
      5200 * lemma44PaperAlpha D * Real.log (lemma23PaperL D) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog.1]
    calc
      _ ≤ (520 * Real.log (lemma23PaperL D)) * (10 * lemma44PaperAlpha D) :=
        mul_le_mul hlog.2 hs.le (norm_nonneg _) (by
          have hh := Real.log_nonneg (show 1 ≤ lemma23PaperL D by linarith)
          positivity)
      _ = _ := by ring
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith : x ≠ 0)),
    ← Complex.ofReal_log (by linarith : 0 ≤ x)]
  calc
    _ ≤ 2 * ‖(Real.log x : ℂ) * (s - 1)‖ :=
      Complex.norm_exp_sub_one_le (hz.trans (lemma54_disk_window_exponent_budget hL))
    _ ≤ 2 * (5200 * lemma44PaperAlpha D * Real.log (lemma23PaperL D)) :=
      mul_le_mul_of_nonneg_left hz (by norm_num)
    _ = _ := by ring

theorem lemma54_disk_window_weighted_error_pointwise {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) {x : ℝ}
    (hx : x ∈ lemma54PaperWindow D) :
    ‖((x : ℂ) ^ (s - 1) - 1) * (lemma54PaperGaussian D x : ℂ)‖ ≤
      (10400 * lemma44PaperAlpha D * Real.log (lemma23PaperL D)) * lemma54PaperGaussian D x := by
  have hg : 0 ≤ lemma54PaperGaussian D x :=
    (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_right (lemma54_disk_window_weight_error hL hs hx)
    (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le

theorem lemma54_disk_window_weighted_error_integrable {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    IntegrableOn (fun x : ℝ => ((x : ℂ) ^ (s - 1) - 1) *
      (lemma54PaperGaussian D x : ℂ)) (lemma54PaperWindow D) := by
  have hi : IntegrableOn (fun x : ℝ =>
      (10400 * lemma44PaperAlpha D * Real.log (lemma23PaperL D)) * lemma54PaperGaussian D x)
      (lemma54PaperWindow D) :=
    ((lemma54_actual_gaussian_mass hD).1.const_mul _).integrableOn
  apply hi.mono'
  · have hm : Measurable (fun x : ℝ => ((x : ℂ) ^ (s - 1) - 1) *
        (lemma54PaperGaussian D x : ℂ)) := by
      unfold lemma54PaperGaussian lemma54GaussianDensity
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (lemma54_window_measurable D)] with x hx
    exact lemma54_disk_window_weighted_error_pointwise hD hL hs hx

theorem lemma54_disk_window_weighted_error_integral {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖∫ x : ℝ in lemma54PaperWindow D, ((x : ℂ) ^ (s - 1) - 1) *
      (lemma54PaperGaussian D x : ℂ)‖ ≤
        10400 * lemma44PaperAlpha D * Real.log (lemma23PaperL D) := by
  let K := 10400 * lemma44PaperAlpha D * Real.log (lemma23PaperL D)
  have hK : 0 ≤ K := by
    have ha := (lemma54_disk_alpha_small hL).1
    have hl := Real.log_nonneg (show 1 ≤ lemma23PaperL D by linarith)
    dsimp [K]
    positivity
  have hi : IntegrableOn (fun x : ℝ => K * lemma54PaperGaussian D x) (lemma54PaperWindow D) :=
    ((lemma54_actual_gaussian_mass hD).1.const_mul K).integrableOn
  calc
    _ ≤ ∫ x : ℝ in lemma54PaperWindow D, K * lemma54PaperGaussian D x := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem (lemma54_window_measurable D)] with x hx
      exact lemma54_disk_window_weighted_error_pointwise hD hL hs hx
    _ = K * ∫ x : ℝ in lemma54PaperWindow D, lemma54PaperGaussian D x := integral_const_mul _ _
    _ ≤ K * ∫ x : ℝ, lemma54PaperGaussian D x := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply setIntegral_le_integral (lemma54_actual_gaussian_mass hD).1
      exact Eventually.of_forall fun x => (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le
    _ = _ := by rw [(lemma54_actual_gaussian_mass hD).2, mul_one]

theorem lemma54_disk_window_gaussian_mellin_integrable {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) *
      (lemma54PaperGaussian D x : ℂ)) (lemma54PaperWindow D) := by
  have hg : IntegrableOn (fun x : ℝ => (lemma54PaperGaussian D x : ℂ))
      (lemma54PaperWindow D) := (lemma54_actual_gaussian_mass hD).1.integrableOn.ofReal
  apply ((lemma54_disk_window_weighted_error_integrable hD hL hs).add hg).congr
  exact Eventually.of_forall fun x => by dsimp only [Pi.add_apply]; ring

theorem lemma54_disk_window_gaussian_mellin_normalization {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖(∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) *
      (lemma54PaperGaussian D x : ℂ)) - 1‖ ≤
        10400 * lemma44PaperAlpha D * Real.log (lemma23PaperL D) +
          2 * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have hg : IntegrableOn (fun x : ℝ => (lemma54PaperGaussian D x : ℂ))
      (lemma54PaperWindow D) := (lemma54_actual_gaussian_mass hD).1.integrableOn.ofReal
  have hw := lemma54_disk_window_gaussian_mellin_integrable hD hL hs
  have hid : (∫ x : ℝ in lemma54PaperWindow D, ((x : ℂ) ^ (s - 1) - 1) *
      (lemma54PaperGaussian D x : ℂ)) =
      (∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) *
        (lemma54PaperGaussian D x : ℂ)) -
          (∫ x : ℝ in lemma54PaperWindow D, (lemma54PaperGaussian D x : ℂ)) := by
    calc
      _ = ∫ x : ℝ in lemma54PaperWindow D,
          (x : ℂ) ^ (s - 1) * (lemma54PaperGaussian D x : ℂ) -
            (lemma54PaperGaussian D x : ℂ) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := integral_sub hw hg
  have heq : (∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) *
      (lemma54PaperGaussian D x : ℂ)) - 1 =
      (∫ x : ℝ in lemma54PaperWindow D, ((x : ℂ) ^ (s - 1) - 1) *
        (lemma54PaperGaussian D x : ℂ)) +
          (((∫ x : ℝ in lemma54PaperWindow D, lemma54PaperGaussian D x : ℝ) - (1 : ℝ) : ℝ) : ℂ) := by
    rw [hid, integral_complex_ofReal, ofReal_sub, ofReal_one]
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add (lemma54_disk_window_weighted_error_integral hD hL hs)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact lemma54_actual_gaussian_window_mass hD hL

end ZhangLS.Spec
