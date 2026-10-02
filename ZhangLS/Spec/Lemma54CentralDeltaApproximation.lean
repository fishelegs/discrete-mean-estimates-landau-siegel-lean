import ZhangLS.Spec.Lemma54CentralMellinWeight

/-! # The actual inverse Mellin Delta on the original central window -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000

theorem lemma54_disk_window_weight_norm {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {s : ℂ} (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D)
    {x : ℝ} (hx : x ∈ lemma54PaperWindow D) :
    ‖(x : ℂ) ^ (s - 1)‖ ≤ 3 := by
  have hh := lemma54_disk_window_weight_error hL hs hx
  have hb := lemma54_disk_window_exponent_budget hL
  calc
    _ = ‖((x : ℂ) ^ (s - 1) - 1) + 1‖ := by congr 1; ring
    _ ≤ ‖(x : ℂ) ^ (s - 1) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 := by rw [norm_one]; linarith

theorem lemma54_disk_window_delta_error_pointwise {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) {x : ℝ}
    (hx : x ∈ lemma54PaperWindow D) :
    ‖(x : ℂ) ^ (s - 1) * (lemma53PaperDelta D x - (lemma54PaperGaussian D x : ℂ))‖ ≤
      (3 * lemma44PaperAlpha D) * lemma54PaperGaussian D x +
        3 * lemma53SmallErrorConstant * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have hxb := lemma54_window_x_bounds hL hx
  have hg : 0 ≤ lemma54PaperGaussian D x :=
    (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le
  have hb := lemma53_small_range_estimate hD hL (by linarith : 0 < x) hxb.2.2.2
  rw [lemma54_actual_omega_eq_gaussian, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hg] at hb
  rw [norm_mul]
  calc
    _ ≤ 3 * (lemma44PaperAlpha D * lemma54PaperGaussian D x +
        lemma53SmallErrorConstant * Real.exp (-(lemma23PaperL D ^ 10) / 2)) :=
      mul_le_mul (lemma54_disk_window_weight_norm hL hs hx) hb (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem lemma54_disk_window_actual_mellin_integrable {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x)
      (lemma54PaperWindow D) := by
  have hr := (lemma54_disk_closed_strip hL hs).1
  have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x) (Ioi 0) :=
    lemma54_mellin_convergent hD hL (by linarith : 0 < s.re)
  apply hi.mono_set
  intro x hx
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (lemma54_window_x_bounds hL hx).1

theorem lemma54_disk_window_delta_error_integral {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) *
      (lemma53PaperDelta D x - (lemma54PaperGaussian D x : ℂ))‖ ≤
      3 * lemma44PaperAlpha D + 6 * lemma53SmallErrorConstant *
        lemma23PaperL D ^ 405 * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  let E := Real.exp (-(lemma23PaperL D ^ 10) / 2)
  have ha := (lemma54_disk_alpha_small hL).1
  have hw : 0 ≤ lemma23PaperL D ^ 405 := pow_nonneg (by linarith) _
  have hgi : IntegrableOn (fun x : ℝ => (3 * lemma44PaperAlpha D) * lemma54PaperGaussian D x)
      (lemma54PaperWindow D) := ((lemma54_actual_gaussian_mass hD).1.const_mul _).integrableOn
  have hci : IntegrableOn (fun _ : ℝ => 3 * lemma53SmallErrorConstant * E)
      (lemma54PaperWindow D) := integrableOn_const (hs := measure_Icc_lt_top.ne)
  have hi : IntegrableOn (fun x : ℝ => (3 * lemma44PaperAlpha D) * lemma54PaperGaussian D x +
      3 * lemma53SmallErrorConstant * E) (lemma54PaperWindow D) :=
    hgi.add hci
  have hmass : (∫ x : ℝ in lemma54PaperWindow D, lemma54PaperGaussian D x) ≤ 1 := by
    rw [← (lemma54_actual_gaussian_mass hD).2]
    apply setIntegral_le_integral (lemma54_actual_gaussian_mass hD).1
    exact Eventually.of_forall fun x => (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le
  calc
    _ ≤ ∫ x : ℝ in lemma54PaperWindow D,
        (3 * lemma44PaperAlpha D) * lemma54PaperGaussian D x + 3 * lemma53SmallErrorConstant * E := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem (lemma54_window_measurable D)] with x hx
      exact lemma54_disk_window_delta_error_pointwise hD hL hs hx
    _ = (3 * lemma44PaperAlpha D) *
        (∫ x : ℝ in lemma54PaperWindow D, lemma54PaperGaussian D x) +
          6 * lemma53SmallErrorConstant * lemma23PaperL D ^ 405 * E := by
      rw [integral_add hgi hci, integral_const_mul]
      unfold lemma54PaperWindow
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 3 * lemma44PaperAlpha D)
      dsimp [E] at *
      linarith

theorem lemma54_disk_window_actual_mellin_normalization {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖(∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x) - 1‖ ≤
      10400 * lemma44PaperAlpha D * Real.log (lemma23PaperL D) + 3 * lemma44PaperAlpha D +
        (2 + 6 * lemma53SmallErrorConstant * lemma23PaperL D ^ 405) *
          Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have ha := lemma54_disk_window_actual_mellin_integrable hD hL hs
  have hg := lemma54_disk_window_gaussian_mellin_integrable hD hL hs
  have hid : (∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) *
      (lemma53PaperDelta D x - (lemma54PaperGaussian D x : ℂ))) =
      (∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x) -
        (∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) * (lemma54PaperGaussian D x : ℂ)) := by
    simp_rw [mul_sub]
    exact integral_sub ha hg
  have heq : (∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x) - 1 =
      (∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) *
        (lemma53PaperDelta D x - (lemma54PaperGaussian D x : ℂ))) +
          ((∫ x : ℝ in lemma54PaperWindow D, (x : ℂ) ^ (s - 1) * (lemma54PaperGaussian D x : ℂ)) - 1) := by
    rw [hid]
    ring
  rw [heq]
  have hh := (norm_add_le _ _).trans (add_le_add
    (lemma54_disk_window_delta_error_integral hD hL hs)
    (lemma54_disk_window_gaussian_mellin_normalization hD hL hs))
  nlinarith only [hh]

end ZhangLS.Spec
