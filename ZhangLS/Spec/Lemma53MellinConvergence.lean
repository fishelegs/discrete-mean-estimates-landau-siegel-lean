import ZhangLS.Spec.Lemma53Kernels

/-! # Absolute convergence of the actual defining Mellin integral -/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma53_omega_norm_vertical {D : ℕ} (hD : 1 < D) (σ t : ℝ) :
    ‖lemma53PaperOmega D ((σ : ℂ) + (t : ℂ) * I)‖ =
      Real.sqrt Real.pi / lemma53PaperScale D *
        Real.exp (((σ - 1 / 2) ^ 2 - (t - (lemma23PaperCenter D).im) ^ 2) /
          (4 * lemma53PaperScale D ^ 2)) := by
  have hB := lemma53_scale_pos hD
  have hc : 0 ≤ Real.sqrt Real.pi / lemma53PaperScale D := by positivity
  unfold lemma53PaperOmega
  rw [norm_mul, Complex.norm_of_nonneg hc, norm_exp]
  congr 2
  have hden : 4 * (lemma53PaperScale D : ℂ) ^ 2 =
      ((4 * lemma53PaperScale D ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hden, div_ofReal_re, pow_two, mul_re]
  simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im,
    ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
    zero_add, add_zero, mul_one, one_mul]
  have hre : (lemma23PaperCenter D).re = 1 / 2 := rfl
  rw [hre]
  ring

theorem lemma53_theta_star_norm_vertical (σ t : ℝ) :
    ‖lemma53PaperThetaStar ((σ : ℂ) + (t : ℂ) * I)‖ =
      (2 * Real.pi) ^ (-σ) * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ *
        Real.exp (Real.pi * t / 2) := by
  unfold lemma53PaperThetaStar
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (by positivity), norm_exp]
  have hre : (-((σ : ℂ) + (t : ℂ) * I)).re = -σ := by simp
  rw [hre]
  congr 2
  simp [mul_re, mul_im]
  ring

noncomputable def lemma53MellinIntegrand (D : ℕ) (x t : ℝ) : ℂ :=
  (x : ℂ) ^ (-((3 / 2 : ℂ) + (t : ℂ) * I)) *
    lemma53PaperThetaStar ((3 / 2 : ℂ) + (t : ℂ) * I) *
    lemma53PaperOmega D ((3 / 2 : ℂ) + (t : ℂ) * I)

theorem lemma53_mellin_integrand_bound {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x)
    (t : ℝ) :
    ‖lemma53MellinIntegrand D x t‖ ≤
      (x ^ (-3 / 2 : ℝ) * (2 * Real.pi) ^ (-3 / 2 : ℝ) * 2 *
        (Real.sqrt Real.pi / lemma53PaperScale D)) *
        Real.exp (Real.pi * t / 2 + (1 - (t - (lemma23PaperCenter D).im) ^ 2) /
          (4 * lemma53PaperScale D ^ 2)) := by
  have hg : ‖Complex.Gamma ((3 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ 2 := by
    have h := lemma44_norm_Gamma_le_factorial (z := (3 / 2 : ℂ) + (t : ℂ) * I)
      (m := 1) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hθ := lemma53_theta_star_norm_vertical (3 / 2) t
  have hω := lemma53_omega_norm_vertical hD (3 / 2) t
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hθ hω
  unfold lemma53MellinIntegrand
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, hθ, hω]
  have hre : (-((3 / 2 : ℂ) + (t : ℂ) * I)).re = -3 / 2 := by simp; norm_num
  rw [hre]
  norm_num only [show (3 / 2 - 1 / 2 : ℝ) = 1 by norm_num, one_pow]
  rw [Real.exp_add]
  have hB := lemma53_scale_pos hD
  have hcoef : 0 ≤ x ^ (-3 / 2 : ℝ) * (2 * Real.pi) ^ (-3 / 2 : ℝ) *
      (Real.sqrt Real.pi / lemma53PaperScale D) *
      Real.exp (Real.pi * t / 2) *
      Real.exp ((1 - (t - (lemma23PaperCenter D).im) ^ 2) / (4 * lemma53PaperScale D ^ 2)) := by
    positivity
  nlinarith only [mul_le_mul_of_nonneg_left hg hcoef]

theorem lemma53_mellin_integrand_integrable {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    Integrable (lemma53MellinIntegrand D x) := by
  let B := lemma53PaperScale D
  let T := (lemma23PaperCenter D).im
  let K := x ^ (-3 / 2 : ℝ) * (2 * Real.pi) ^ (-3 / 2 : ℝ) * 2 * (Real.sqrt Real.pi / B)
  have hB : 0 < B := lemma53_scale_pos hD
  let b : ℝ := -(4 * B ^ 2)⁻¹
  let c : ℝ := Real.pi / 2 + 2 * T / (4 * B ^ 2)
  let d : ℝ := (1 - T ^ 2) / (4 * B ^ 2)
  have hb : (b : ℂ).re < 0 := by
    change -(4 * B ^ 2)⁻¹ < 0
    exact neg_lt_zero.mpr (inv_pos.mpr (by positivity))
  have hg := (integrable_cexp_quadratic' hb (c : ℂ) (d : ℂ)).norm.const_mul K
  have he (t : ℝ) : ‖Complex.exp ((b : ℂ) * (t : ℂ) ^ 2 + (c : ℂ) * t + d)‖ =
      Real.exp (Real.pi * t / 2 + (1 - (t - T) ^ 2) / (4 * B ^ 2)) := by
    rw [norm_exp]
    congr 1
    simp only [mul_re, add_re, ofReal_re, ofReal_im, ← ofReal_pow, mul_zero, sub_zero]
    dsimp [b, c, d]
    ring
  apply hg.mono'
  · apply Continuous.aestronglyMeasurable
    have hΓ : Continuous (fun t : ℝ => Complex.Gamma ((3 / 2 : ℂ) + (t : ℂ) * I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (Complex.differentiableAt_Gamma _ (by
        intro n hn
        have hh := congrArg Complex.re hn
        simp at hh
        nlinarith)).continuousAt.comp (by fun_prop)
    unfold lemma53MellinIntegrand lemma53PaperThetaStar lemma53PaperOmega
    have hxp : Continuous (fun t : ℝ => (x : ℂ) ^ (-((3 / 2 : ℂ) + (t : ℂ) * I))) := by
      rw [show (fun t : ℝ => (x : ℂ) ^ (-((3 / 2 : ℂ) + (t : ℂ) * I))) =
        (fun t : ℝ => Complex.exp (Complex.log (x : ℂ) * (-((3 / 2 : ℂ) + (t : ℂ) * I)))) by
          funext t; rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]]
      fun_prop
    have hπp : Continuous (fun t : ℝ => ((2 * Real.pi : ℝ) : ℂ) ^
        (-((3 / 2 : ℂ) + (t : ℂ) * I))) := by
      simp_rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr
        (show (2 * Real.pi : ℝ) ≠ 0 by positivity))]
      fun_prop
    exact ((hxp.mul ((hπp.mul hΓ).mul (by fun_prop))).mul (by fun_prop))
  · filter_upwards [] with t
    rw [he]
    exact lemma53_mellin_integrand_bound hD hx t

theorem lemma53_defining_mellin_integrable {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-((3 / 2 : ℂ) + (t : ℂ) * I)) *
      (lemma53PaperThetaStar ((3 / 2 : ℂ) + (t : ℂ) * I) *
        lemma53PaperOmega D ((3 / 2 : ℂ) + (t : ℂ) * I))) := by
  have h := lemma53_mellin_integrand_integrable hD hx
  unfold lemma53MellinIntegrand at h
  simpa only [mul_assoc] using h

end ZhangLS.Spec
