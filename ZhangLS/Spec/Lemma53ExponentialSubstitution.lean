import ZhangLS.Spec.Lemma53RegularizedMellin
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Exponential substitution and convergence of the log-Gaussian integral -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma53_exp_change_of_variables (f : ℝ → ℂ) :
    (∫ y : ℝ in Ioi 0, f y) = ∫ u : ℝ, (Real.exp u : ℂ) * f (Real.exp u) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u (_ : u ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn f
  simpa only [image_univ, Real.range_exp, setIntegral_univ,
    abs_of_pos (Real.exp_pos _), Complex.real_smul] using h

noncomputable def lemma53ExponentialKernel (D : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (lemma23PaperCenter D * (u : ℂ) -
    (lemma53PaperScale D : ℂ) ^ 2 * (u : ℂ) ^ 2 - z * (Real.exp u : ℂ))

theorem lemma53_log_gaussian_after_exp (D : ℕ) (z : ℂ) (u : ℝ) :
    (Real.exp u : ℂ) * lemma53LogGaussianKernel D z (Real.exp u) =
      lemma53ExponentialKernel D z u := by
  unfold lemma53LogGaussianKernel lemma53ExponentialKernel
  rw [Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

theorem lemma53_exponential_kernel_norm (D : ℕ) (z : ℂ) (u : ℝ) :
    ‖lemma53ExponentialKernel D z u‖ =
      Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2 - z.re * Real.exp u) := by
  unfold lemma53ExponentialKernel
  rw [norm_exp]
  congr 1
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, ← ofReal_pow,
    mul_zero, sub_zero, lemma23PaperCenter]
  simp
  ring

theorem lemma53_exponential_kernel_integrable {D : ℕ} (hD : 1 < D)
    {z : ℂ} (hz : 0 ≤ z.re) : Integrable (lemma53ExponentialKernel D z) := by
  have hg := (lemma53_gaussian_laplace_integrable (lemma53_scale_pos hD) (1 / 2)).norm
  apply hg.mono'
  · unfold lemma53ExponentialKernel
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · filter_upwards [] with u
    rw [lemma53_exponential_kernel_norm, norm_exp]
    have hre : ((1 / 2 : ℂ) * (u : ℂ) -
        (lemma53PaperScale D : ℂ) ^ 2 * (u : ℂ) ^ 2).re =
        u / 2 - lemma53PaperScale D ^ 2 * u ^ 2 := by
      simp only [← Complex.ofReal_pow, sub_re, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero]
      norm_num
      ring
    rw [hre]
    apply Real.exp_le_exp.mpr
    have hnonneg := mul_nonneg hz (Real.exp_pos u).le
    linarith

theorem lemma53_log_gaussian_integrable {D : ℕ} (hD : 1 < D)
    {z : ℂ} (hz : 0 ≤ z.re) :
    IntegrableOn (lemma53LogGaussianKernel D z) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u (_ : u ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn (lemma53LogGaussianKernel D z)
  simp only [image_univ, Real.range_exp, integrableOn_univ,
    abs_of_pos (Real.exp_pos _), Complex.real_smul, lemma53_log_gaussian_after_exp] at h
  exact h.mpr (lemma53_exponential_kernel_integrable hD hz)

theorem lemma53_regularized_mellin_exponential {D : ℕ} (hD : 1 < D)
    {z : ℂ} (hz : 0 < z.re) :
    lemma53RegularizedMellin D z = ∫ u : ℝ, lemma53ExponentialKernel D z u := by
  rw [lemma53_regularized_mellin hD hz, lemma53_exp_change_of_variables]
  simp_rw [lemma53_log_gaussian_after_exp]

end ZhangLS.Spec
