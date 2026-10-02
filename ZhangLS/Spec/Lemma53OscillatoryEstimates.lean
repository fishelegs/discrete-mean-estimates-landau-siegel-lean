import ZhangLS.Spec.Lemma53Kernels

/-! # Unconditional convergence and perturbation bounds for the oscillatory kernel -/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma53_oscillatory_kernel_norm_real (D : ℕ) (x u : ℝ) :
    ‖lemma53OscillatoryKernel D x (u : ℂ)‖ =
      Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) := by
  unfold lemma53OscillatoryKernel
  rw [Complex.norm_exp]
  congr 1
  simp [lemma23PaperCenter, mul_re, exp_ofReal_im, ← ofReal_pow]
  ring

theorem lemma53_oscillatory_kernel_integrable {D : ℕ} (hD : 1 < D) (x : ℝ) :
    Integrable (fun u : ℝ => lemma53OscillatoryKernel D x (u : ℂ)) := by
  have hg := (lemma53_gaussian_laplace_integrable (lemma53_scale_pos hD) (1 / 2)).norm
  apply hg.mono'
  · apply Continuous.aestronglyMeasurable
    unfold lemma53OscillatoryKernel
    fun_prop
  · filter_upwards [] with u
    rw [lemma53_oscillatory_kernel_norm_real, norm_exp]
    apply le_of_eq
    congr 1
    simp [mul_re, ← ofReal_pow]
    ring

theorem lemma53_oscillatory_delta_norm_bound {D : ℕ} (hD : 1 < D) (x : ℝ) :
    ‖lemma53OscillatoryDelta D x‖ ≤
      Real.sqrt Real.pi / lemma53PaperScale D *
        Real.exp (1 / (16 * lemma53PaperScale D ^ 2)) := by
  have hg := lemma53_gaussian_laplace (lemma53_scale_pos hD) (1 / 2)
  have hnorm : ∀ u : ℝ, ‖lemma53OscillatoryKernel D x (u : ℂ)‖ =
      (Complex.exp ((1 / 2 : ℂ) * (u : ℂ) - (lemma53PaperScale D : ℂ) ^ 2 * (u : ℂ) ^ 2)).re := by
    intro u
    rw [lemma53_oscillatory_kernel_norm_real, Complex.exp_re]
    simp [mul_re, ← ofReal_pow]
    ring
  have hre := congrArg Complex.re hg
  unfold lemma53OscillatoryDelta
  apply (norm_integral_le_integral_norm _).trans
  simp_rw [hnorm]
  have hlin := integral_re (lemma53_gaussian_laplace_integrable (lemma53_scale_pos hD) (1 / 2))
  simp only [RCLike.re_eq_complex_re] at hlin
  rw [hlin]
  rw [hre]
  apply le_of_eq
  have he : (1 / 2 : ℂ) ^ 2 / (4 * (lemma53PaperScale D : ℂ) ^ 2) =
      ((1 / (16 * lemma53PaperScale D ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, exp_ofReal_re]

theorem lemma53_perturbation_norm_bound {x : ℝ} (hx : 0 ≤ x) {w : ℂ}
    (hw : ‖w‖ ≤ 1) :
    ‖w / 2 - (2 * Real.pi : ℂ) * I * (x : ℂ) * (Complex.exp w - 1 - w)‖ ≤
      ‖w‖ / 2 + 2 * Real.pi * x * ‖w‖ ^ 2 := by
  have hrest := Complex.norm_exp_sub_one_sub_id_le hw
  have hnorm : ‖(2 * Real.pi : ℂ) * I * (x : ℂ)‖ = 2 * Real.pi * x := by
    simp [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
      abs_of_pos Real.pi_pos]
  calc
    _ ≤ ‖w / 2‖ + ‖(2 * Real.pi : ℂ) * I * (x : ℂ) * (Complex.exp w - 1 - w)‖ :=
      norm_sub_le _ _
    _ = ‖w‖ / 2 + (2 * Real.pi * x) * ‖Complex.exp w - 1 - w‖ := by
      rw [norm_div, norm_mul, hnorm]
      norm_num
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hrest (by positivity))

theorem lemma53_perturbation_sub_one_bound {x : ℝ} (hx : 0 ≤ x) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (hsmall : ‖w‖ / 2 + 2 * Real.pi * x * ‖w‖ ^ 2 ≤ 1) :
    ‖lemma53Perturbation x w - 1‖ ≤ ‖w‖ + 4 * Real.pi * x * ‖w‖ ^ 2 := by
  have hb := lemma53_perturbation_norm_bound hx hw
  have h := Complex.norm_exp_sub_one_le (hb.trans hsmall)
  unfold lemma53Perturbation
  nlinarith

theorem lemma53_kernel_error_factorization (D : ℕ) (x : ℝ) (w : ℂ) :
    lemma53OscillatoryKernel D x w - lemma53GaussianPhase D x w =
      lemma53GaussianPhase D x w * (lemma53Perturbation x w - 1) := by
  rw [lemma53_kernel_factorization]
  ring

/-- The exact real part controlling both contour shifts in the paper.
This form also includes v=0, without dividing by v. -/
theorem lemma53_oscillatory_kernel_norm_shifted (D : ℕ) (x u v : ℝ) :
    ‖lemma53OscillatoryKernel D x ((u : ℂ) + (v : ℂ) * I)‖ =
      Real.exp (u / 2 - lemma53PaperScale D ^ 2 * (u ^ 2 - v ^ 2) -
        2 * Real.pi * lemma51PaperT0 D * v +
        2 * Real.pi * x * Real.exp u * Real.sin v) := by
  unfold lemma53OscillatoryKernel
  rw [norm_exp]
  congr 1
  simp [lemma23PaperCenter, lemma51PaperT0, mul_re, mul_im, pow_two, exp_im,
    ← ofReal_pow]
  ring

theorem lemma53_gaussian_phase_norm_shifted (D : ℕ) (x u v : ℝ) :
    ‖lemma53GaussianPhase D x ((u : ℂ) + (v : ℂ) * I)‖ =
      Real.exp (-2 * Real.pi * (lemma51PaperT0 D - x) * v -
        lemma53PaperScale D ^ 2 * (u ^ 2 - v ^ 2)) := by
  unfold lemma53GaussianPhase
  rw [norm_exp]
  congr 1
  simp [mul_re, mul_im, pow_two, ← ofReal_pow]

/-- On the stationary horizontal line the Gaussian is its real-axis
envelope times the original frequency Gaussian. -/
theorem lemma53_gaussian_phase_norm_at_stationary_line {D : ℕ} (hD : 1 < D)
    (x u : ℝ) :
    ‖lemma53GaussianPhase D x ((u : ℂ) +
        (Real.pi * (lemma51PaperT0 D - x) / lemma53PaperScale D ^ 2 : ℝ) * I)‖ =
      Real.exp (-(lemma53PaperScale D ^ 2 * u ^ 2) -
        (Real.pi * (lemma51PaperT0 D - x) / lemma53PaperScale D) ^ 2) := by
  rw [lemma53_gaussian_phase_norm_shifted]
  congr 1
  field_simp [(lemma53_scale_pos hD).ne']
  ring

end ZhangLS.Spec
