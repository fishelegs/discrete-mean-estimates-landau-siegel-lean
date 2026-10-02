import ZhangLS.Spec.Lemma53GaussianInverse
import ZhangLS.Spec.Lemma53GammaLaplace
import ZhangLS.Spec.Lemma53MellinConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! # Absolutely convergent regularized Gamma--Gaussian Mellin inversion -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000

noncomputable def lemma53MellinLine (t : ℝ) : ℂ := (3 / 2 : ℂ) + (t : ℂ) * I

noncomputable def lemma53RegularizedMellin (D : ℕ) (z : ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
    z ^ (-lemma53MellinLine t) * Complex.Gamma (lemma53MellinLine t) *
      lemma53PaperOmega D (lemma53MellinLine t)

noncomputable def lemma53GammaGaussianKernel (D : ℕ) (z : ℂ) (t y : ℝ) : ℂ :=
  Complex.exp ((lemma53MellinLine t - 1) * (Real.log y : ℂ) - z * (y : ℂ)) *
    lemma53PaperOmega D (lemma53MellinLine t)

noncomputable def lemma53LogGaussianKernel (D : ℕ) (z : ℂ) (y : ℝ) : ℂ :=
  Complex.exp ((lemma23PaperCenter D - 1) * (Real.log y : ℂ) -
    (lemma53PaperScale D : ℂ) ^ 2 * (Real.log y : ℂ) ^ 2 - z * (y : ℂ))

theorem lemma53_omega_vertical_integrable {D : ℕ} (hD : 1 < D) :
    Integrable (fun t : ℝ => lemma53PaperOmega D (lemma53MellinLine t)) := by
  simpa [lemma53MellinLine, lemma53PaperOmega] using
    (lemma53_gaussian_inverse_integrable (lemma53_scale_pos hD)
      (lemma23PaperCenter D) (3 / 2) zero_lt_one)

theorem lemma53_gamma_gaussian_kernel_eq (D : ℕ) (z : ℂ) (t : ℝ)
    {y : ℝ} (hy : 0 < y) :
    lemma53GammaGaussianKernel D z t y =
      lemma53GammaLaplaceKernel (lemma53MellinLine t) z y *
        lemma53PaperOmega D (lemma53MellinLine t) := by
  unfold lemma53GammaGaussianKernel lemma53GammaLaplaceKernel
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hy.ne'), ← ofReal_log hy.le,
    sub_eq_add_neg, Complex.exp_add]
  congr 2 <;> congr 1 <;> ring

theorem lemma53_gamma_gaussian_kernel_norm (D : ℕ) (z : ℂ) (t : ℝ)
    {y : ℝ} (hy : 0 < y) :
    ‖lemma53GammaGaussianKernel D z t y‖ =
      y ^ (1 / 2 : ℝ) * Real.exp (-z.re * y) *
        ‖lemma53PaperOmega D (lemma53MellinLine t)‖ := by
  rw [lemma53_gamma_gaussian_kernel_eq D z t hy, norm_mul,
    lemma53_gamma_laplace_kernel_norm _ _ hy]
  congr 3
  simp [lemma53MellinLine]
  norm_num

theorem lemma53_gamma_gaussian_product_integrable {D : ℕ} (hD : 1 < D)
    {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun p : ℝ × ℝ => lemma53GammaGaussianKernel D z p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hmajor := (lemma53_omega_vertical_integrable hD).norm.mul_prod
    (lemma53_rpow_laplace_integrable (a := (1 / 2 : ℝ)) (by norm_num) hz)
  apply hmajor.mono'
  · apply Measurable.aestronglyMeasurable
    unfold lemma53GammaGaussianKernel lemma53PaperOmega lemma53MellinLine
    fun_prop
  · have hpos : ∀ᵐ p : ℝ × ℝ ∂volume.prod (volume.restrict (Ioi 0)), 0 < p.2 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
      exact Eventually.of_forall (fun _ => self_mem_ae_restrict measurableSet_Ioi)
    filter_upwards [hpos] with p hp
    rw [lemma53_gamma_gaussian_kernel_norm D z p.1 hp]
    exact le_of_eq (mul_comm _ _)

theorem lemma53_gamma_gaussian_inner_y (D : ℕ) {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    (∫ y : ℝ in Ioi 0, lemma53GammaGaussianKernel D z t y) =
      z ^ (-lemma53MellinLine t) * Complex.Gamma (lemma53MellinLine t) *
        lemma53PaperOmega D (lemma53MellinLine t) := by
  rw [show (∫ y : ℝ in Ioi 0, lemma53GammaGaussianKernel D z t y) =
      ∫ y : ℝ in Ioi 0, lemma53GammaLaplaceKernel (lemma53MellinLine t) z y *
        lemma53PaperOmega D (lemma53MellinLine t) from
      setIntegral_congr_fun measurableSet_Ioi (fun y hy =>
        lemma53_gamma_gaussian_kernel_eq D z t hy)]
  rw [integral_mul_const, ← lemma53GammaLaplace,
    lemma53_gamma_laplace (by norm_num [lemma53MellinLine]) hz]

theorem lemma53_gamma_gaussian_inner_t {D : ℕ} (hD : 1 < D) (z : ℂ)
    {y : ℝ} (hy : 0 < y) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, lemma53GammaGaussianKernel D z t y) =
        lemma53LogGaussianKernel D z y := by
  let K : ℂ := Complex.exp (-(Real.log y : ℂ) - z * (y : ℂ))
  have he (t : ℝ) : lemma53GammaGaussianKernel D z t y =
      K * ((y⁻¹ : ℂ) ^ (-lemma53MellinLine t) *
        lemma53PaperOmega D (lemma53MellinLine t)) := by
    unfold lemma53GammaGaussianKernel
    rw [Complex.cpow_def_of_ne_zero (inv_ne_zero (ofReal_ne_zero.mpr hy.ne')),
      ← ofReal_inv, ← ofReal_log (inv_pos.mpr hy).le, Real.log_inv]
    dsimp [K]
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul]
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (K * ∫ t : ℝ, (y⁻¹ : ℂ) ^ (-lemma53MellinLine t) *
        lemma53PaperOmega D (lemma53MellinLine t)) =
      K * mellinInv (3 / 2) (lemma53PaperOmega D) y⁻¹ by
      unfold mellinInv lemma53MellinLine
      simp only [Complex.real_smul, smul_eq_mul, ofReal_div, ofReal_ofNat, ofReal_inv]
      ring]
  rw [lemma53_omega_inverse hD (3 / 2) (inv_pos.mpr hy)]
  dsimp [K, lemma53LogGaussianKernel]
  rw [← Complex.exp_add, Real.log_inv]
  push_cast
  congr 1
  ring

theorem lemma53_regularized_mellin {D : ℕ} (hD : 1 < D) {z : ℂ} (hz : 0 < z.re) :
    lemma53RegularizedMellin D z =
      ∫ y : ℝ in Ioi 0, lemma53LogGaussianKernel D z y := by
  unfold lemma53RegularizedMellin
  simp_rw [← lemma53_gamma_gaussian_inner_y D hz]
  rw [integral_integral_swap (lemma53_gamma_gaussian_product_integrable hD hz),
    ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi
    (fun y hy => lemma53_gamma_gaussian_inner_t hD z hy)

end ZhangLS.Spec
