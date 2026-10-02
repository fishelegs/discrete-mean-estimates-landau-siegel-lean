import ZhangLS.Spec.Lemma54UniformSecondMoment
import ZhangLS.Spec.Lemma57GaussianQuadraticMoment

/-! # The actual positive Gaussian has total real-line mass one -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000

noncomputable def lemma54GaussianDensity (B t x : ℝ) : ℝ :=
  Real.sqrt Real.pi / B * Real.exp (-((Real.pi * (x - t) / B) ^ 2))

noncomputable def lemma54PaperGaussian (D : ℕ) : ℝ → ℝ :=
  lemma54GaussianDensity (lemma53PaperScale D) (lemma51PaperT0 D)

theorem lemma54_gaussian_density_pos {B : ℝ} (hB : 0 < B) (t x : ℝ) :
    0 < lemma54GaussianDensity B t x :=
  mul_pos (div_pos (Real.sqrt_pos.mpr Real.pi_pos) hB) (Real.exp_pos _)

theorem lemma54_gaussian_density_factor (B t x : ℝ) :
    lemma54GaussianDensity B t x =
      Real.sqrt Real.pi / B * Real.exp (-(Real.pi / B) ^ 2 * (x - t) ^ 2) := by
  unfold lemma54GaussianDensity
  congr 2
  ring

theorem lemma54_gaussian_density_integrable {B : ℝ} (hB : 0 < B) (t : ℝ) :
    Integrable (lemma54GaussianDensity B t) := by
  have hi := (lemma54_real_gaussian_integrable (div_pos Real.pi_pos hB) 0).comp_sub_right t
  have heq : lemma54GaussianDensity B t = fun x : ℝ =>
      (Real.sqrt Real.pi / B) *
        Real.exp (0 * (x - t) - (Real.pi / B) ^ 2 * (x - t) ^ 2) := by
    funext x
    rw [lemma54_gaussian_density_factor]
    congr 2
    ring
  rw [heq]
  exact hi.const_mul (Real.sqrt Real.pi / B)

theorem lemma54_gaussian_density_integral {B : ℝ} (hB : 0 < B) (t : ℝ) :
    (∫ x : ℝ, lemma54GaussianDensity B t x) = 1 := by
  have heq : lemma54GaussianDensity B t = fun x : ℝ =>
      (Real.sqrt Real.pi / B) *
        Real.exp (0 * (x - t) - (Real.pi / B) ^ 2 * (x - t) ^ 2) := by
    funext x
    rw [lemma54_gaussian_density_factor]
    congr 2
    ring
  rw [heq, integral_const_mul,
    integral_sub_right_eq_self (fun u : ℝ =>
      Real.exp (0 * u - (Real.pi / B) ^ 2 * u ^ 2)) t]
  have hi := lemma54_real_gaussian_integral (div_pos Real.pi_pos hB) 0
  rw [hi]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, Real.exp_zero, mul_one]
  field_simp [hB.ne', Real.pi_ne_zero]
  nlinarith [Real.sq_sqrt Real.pi_nonneg]

theorem lemma54_actual_omega_eq_gaussian (D : ℕ) (x : ℝ) :
    lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)) =
      (lemma54PaperGaussian D x : ℂ) := lemma53_omega_critical_gaussian D x

theorem lemma54_actual_omega_norm_eq_gaussian {D : ℕ} (hD : 1 < D) (x : ℝ) :
    ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ =
      lemma54PaperGaussian D x := by
  rw [lemma54_actual_omega_eq_gaussian, Complex.norm_of_nonneg]
  exact (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le

theorem lemma54_actual_gaussian_mass {D : ℕ} (hD : 1 < D) :
    Integrable (lemma54PaperGaussian D) ∧ (∫ x : ℝ, lemma54PaperGaussian D x) = 1 :=
  ⟨lemma54_gaussian_density_integrable (lemma53_scale_pos hD) _,
    lemma54_gaussian_density_integral (lemma53_scale_pos hD) _⟩

end ZhangLS.Spec
