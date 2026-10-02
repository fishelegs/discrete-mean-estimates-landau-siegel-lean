import ZhangLS.Spec.Lemma56TwistedGaussianContour

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_gaussian_omega_norm {B : ℝ} (hB : 0 < B) (σ t : ℝ) :
    ‖lemma56GaussianOmega B ((σ : ℂ) + (t : ℂ) * I)‖ =
      (Real.sqrt Real.pi / B) * Real.exp ((σ ^ 2 - t ^ 2) / (4 * B ^ 2)) := by
  rw [lemma56GaussianOmega, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < Real.sqrt Real.pi / B), Complex.norm_exp]
  congr 2
  have hcast : 4 * (B : ℂ) ^ 2 = ((4 * B ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hsq : (((σ : ℂ) + (t : ℂ) * I) ^ 2).re = σ ^ 2 - t ^ 2 := by
    rw [pow_two, Complex.mul_re]
    simp
    ring
  have hinv : (((4 * B ^ 2 : ℝ) : ℂ))⁻¹ = (((4 * B ^ 2)⁻¹ : ℝ) : ℂ) := by norm_cast
  rw [hcast, div_eq_mul_inv, hinv, Complex.mul_re, hsq]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

lemma lemma56_gaussian_kernel_norm {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (σ t : ℝ) :
    ‖lemma56GaussianKernel B σ x t‖ =
      x ^ σ * (Real.sqrt Real.pi / B) *
        Real.exp (σ ^ 2 / (4 * B ^ 2)) * Real.exp (-(1 / (4 * B ^ 2)) * t ^ 2) := by
  rw [lemma56GaussianKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    lemma56_gaussian_omega_norm hB σ t]
  have he : (σ ^ 2 - t ^ 2) / (4 * B ^ 2) =
      σ ^ 2 / (4 * B ^ 2) + (-(1 / (4 * B ^ 2)) * t ^ 2) := by ring
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [he, Real.exp_add]
  ring

lemma lemma56_gaussian_kernel_norm_integral {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (σ : ℝ) :
    (∫ t : ℝ, ‖lemma56GaussianKernel B σ x t‖) =
      2 * Real.pi * x ^ σ * Real.exp (σ ^ 2 / (4 * B ^ 2)) := by
  simp_rw [lemma56_gaussian_kernel_norm hB hx]
  rw [MeasureTheory.integral_const_mul, integral_gaussian]
  have hs : Real.sqrt (Real.pi / (1 / (4 * B ^ 2))) = 2 * B * Real.sqrt Real.pi := by
    have he : Real.pi / (1 / (4 * B ^ 2)) = (2 * B) ^ 2 * Real.pi := by field_simp; ring
    rw [he, Real.sqrt_mul (sq_nonneg (2 * B)), Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * B)]
  rw [hs]
  have hsq := Real.sq_sqrt Real.pi_pos.le
  field_simp
  nlinarith only [hsq]


end ZhangLS.Spec
