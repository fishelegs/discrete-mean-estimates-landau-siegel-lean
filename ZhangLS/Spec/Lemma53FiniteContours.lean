import ZhangLS.Spec.Lemma53MellinIdentity
import ZhangLS.Spec.Lemma44GaussianVerticalTail

/-! # Actual finite contour shifts and Gaussian tails in Lemma 5.3 -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

noncomputable def lemma53ErrorKernel (D : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  lemma53OscillatoryKernel D x w - lemma53GaussianPhase D x w

theorem lemma53_oscillatory_kernel_differentiable (D : ℕ) (x : ℝ) :
    Differentiable ℂ (lemma53OscillatoryKernel D x) := by
  unfold lemma53OscillatoryKernel
  fun_prop

theorem lemma53_error_kernel_differentiable (D : ℕ) (x : ℝ) :
    Differentiable ℂ (lemma53ErrorKernel D x) := by
  unfold lemma53ErrorKernel lemma53OscillatoryKernel lemma53GaussianPhase
  fun_prop

theorem lemma53_entire_rectangle_shift (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a b v : ℝ) :
    (∫ u : ℝ in a..b, f (u : ℂ)) =
      (∫ u : ℝ in a..b, f ((u : ℂ) + (v : ℂ) * I)) +
        I * (∫ y : ℝ in 0..v, f ((a : ℂ) + (y : ℂ) * I)) -
          I * (∫ y : ℝ in 0..v, f ((b : ℂ) + (y : ℂ) * I)) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (a : ℂ) ((b : ℂ) + (v : ℂ) * I) hf.differentiableOn
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    ofReal_zero, mul_zero, zero_mul, sub_zero, mul_one, zero_add, add_zero, smul_eq_mul] at h
  linear_combination h

theorem lemma53_error_rectangle_shift (D : ℕ) (x a b v : ℝ) :
    (∫ u : ℝ in a..b, lemma53ErrorKernel D x (u : ℂ)) =
      (∫ u : ℝ in a..b, lemma53ErrorKernel D x ((u : ℂ) + (v : ℂ) * I)) +
        I * (∫ y : ℝ in 0..v, lemma53ErrorKernel D x ((a : ℂ) + (y : ℂ) * I)) -
          I * (∫ y : ℝ in 0..v, lemma53ErrorKernel D x ((b : ℂ) + (y : ℂ) * I)) :=
  lemma53_entire_rectangle_shift _ (lemma53_error_kernel_differentiable D x) a b v

theorem lemma53_error_kernel_integrable {D : ℕ} (hD : 1 < D) (x : ℝ) :
    Integrable (fun u : ℝ => lemma53ErrorKernel D x (u : ℂ)) :=
  (lemma53_oscillatory_kernel_integrable hD x).sub (lemma53_gaussian_phase_integrable hD x)

theorem lemma53_actual_error_integral {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    lemma53PaperDelta D x -
      lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)) =
        ∫ u : ℝ, lemma53ErrorKernel D x (u : ℂ) := by
  rw [lemma53_mellin_oscillatory_identity hD hx, ← lemma53_gaussian_main_term hD x]
  unfold lemma53OscillatoryDelta lemma53ErrorKernel
  rw [integral_sub (lemma53_oscillatory_kernel_integrable hD x)
    (lemma53_gaussian_phase_integrable hD x)]

theorem lemma53_error_kernel_gaussian_bound {D : ℕ}
    (hB : 1 ≤ lemma53PaperScale D) (x u : ℝ) :
    ‖lemma53ErrorKernel D x (u : ℂ)‖ ≤
      (Real.exp 1 + 1) * Real.exp (-(lemma53PaperScale D ^ 2 / 2) * u ^ 2) := by
  have hBsq : 1 ≤ lemma53PaperScale D ^ 2 := by nlinarith
  have hosc := lemma53_oscillatory_kernel_norm_real D x u
  have hg := lemma53_gaussian_phase_norm_shifted D x u 0
  simp only [ofReal_zero, zero_mul, add_zero, mul_zero, zero_sub, zero_pow,
    sub_zero, neg_zero, zero_add] at hg
  have hquad : u / 2 - lemma53PaperScale D ^ 2 * u ^ 2 ≤
      1 - (lemma53PaperScale D ^ 2 / 2) * u ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hBsq) (sq_nonneg u)
    nlinarith [sq_nonneg (u - 1 / 2)]
  have hosc_le : ‖lemma53OscillatoryKernel D x (u : ℂ)‖ ≤
      Real.exp 1 * Real.exp (-(lemma53PaperScale D ^ 2 / 2) * u ^ 2) := by
    rw [hosc, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hg_le : ‖lemma53GaussianPhase D x (u : ℂ)‖ ≤
      Real.exp (-(lemma53PaperScale D ^ 2 / 2) * u ^ 2) := by
    rw [hg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  exact (norm_sub_le _ _).trans (by
    nlinarith [hosc_le, hg_le])

theorem lemma53_actual_error_truncation {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) {x r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (hBr : 1 ≤ lemma53PaperScale D ^ 2 * r) :
    ‖lemma53PaperDelta D x -
      lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)) -
        (∫ u : ℝ in -r..r, lemma53ErrorKernel D x (u : ℂ))‖ ≤
      4 * (Real.exp 1 + 1) * Real.exp (-(lemma53PaperScale D ^ 2 * r ^ 2) / 2) := by
  rw [lemma53_actual_error_integral hD hx]
  have hb : 0 < lemma53PaperScale D ^ 2 / 2 := by
    have := lemma53_scale_pos hD
    positivity
  have h := lemma44_gaussian_integral_truncation
    (fun u => lemma53ErrorKernel D x (u : ℂ)) (lemma53_error_kernel_integrable hD x)
    (C := Real.exp 1 + 1) (b := lemma53PaperScale D ^ 2 / 2) (T := r)
    (by positivity) hb hr (lemma53_error_kernel_gaussian_bound hB x)
  apply h.trans
  apply (div_le_iff₀ (mul_pos hb hr)).mpr
  have he : 0 < Real.exp (-(lemma53PaperScale D ^ 2 * r ^ 2) / 2) := Real.exp_pos _
  have hh := mul_le_mul_of_nonneg_left hBr
    (show 0 ≤ 2 * (Real.exp 1 + 1) * Real.exp (-(lemma53PaperScale D ^ 2 * r ^ 2) / 2) by positivity)
  convert hh using 1 <;> ring

noncomputable def lemma53SmallRadius (D : ℕ) : ℝ :=
  lemma23PaperL D ^ 5 / lemma53PaperScale D

theorem lemma53_small_radius_scale {D : ℕ} (hD : 1 < D) :
    lemma53PaperScale D ^ 2 * lemma53SmallRadius D ^ 2 = lemma23PaperL D ^ 10 := by
  have hB := (lemma53_scale_pos hD).ne'
  unfold lemma53SmallRadius
  field_simp [hB]

theorem lemma53_small_radius_tail {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x) :
    ‖lemma53PaperDelta D x -
      lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)) -
        (∫ u : ℝ in -lemma53SmallRadius D..lemma53SmallRadius D,
          lemma53ErrorKernel D x (u : ℂ))‖ ≤
      4 * (Real.exp 1 + 1) * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have hB : 1 ≤ lemma53PaperScale D := one_le_pow₀ hL
  have hr : 0 < lemma53SmallRadius D := by
    unfold lemma53SmallRadius
    have := lemma53_scale_pos hD
    have : 0 < lemma23PaperL D := lt_of_lt_of_le zero_lt_one hL
    positivity
  have hBr : 1 ≤ lemma53PaperScale D ^ 2 * lemma53SmallRadius D := by
    have he : lemma53PaperScale D ^ 2 * lemma53SmallRadius D =
        lemma53PaperScale D * lemma23PaperL D ^ 5 := by
      unfold lemma53SmallRadius
      field_simp [(lemma53_scale_pos hD).ne']
    rw [he]
    exact one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hL)
  simpa only [lemma53_small_radius_scale hD] using
    lemma53_actual_error_truncation hD hB hx hr hBr

end ZhangLS.Spec
