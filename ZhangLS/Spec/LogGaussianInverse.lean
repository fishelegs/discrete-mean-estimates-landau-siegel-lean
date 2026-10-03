import ZhangLS.Spec.GaussianVerticalNumerator
import ZhangLS.Spec.LogGaussianWeight

/-! The actual inverse Mellin identity for the squared Perron pole. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
set_option maxHeartbeats 1000000

noncomputable def lemma171LogGaussianKernelIntegrand (D : ℕ) (σ x t : ℝ) : ℂ :=
  (x : ℂ)^((σ : ℂ)+(t : ℂ)*I) * lemma57OmegaOne D ((σ : ℂ)+(t : ℂ)*I) /
    ((σ : ℂ)+(t : ℂ)*I)^2

noncomputable def lemma171LogGaussianKernelVerticalIntegral (D : ℕ) (σ x : ℝ) : ℂ :=
  (2*(Real.pi : ℂ)*I)⁻¹ * ∫ t : ℝ, lemma171LogGaussianKernelIntegrand D σ x t * I

lemma lemma171_gaussian_numerator_eq_cpow (D : ℕ) (σ : ℝ) {x : ℝ} (hx : 0 < x)
    (t : ℝ) :
    lemma171GaussianNumerator (lemma57GaussianLogScale D) σ (Real.log x) t =
      (x : ℂ)^((σ : ℂ)+(t : ℂ)*I) * lemma57OmegaOne D ((σ : ℂ)+(t : ℂ)*I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  unfold lemma57OmegaOne lemma171GaussianNumerator
  rw [← Complex.exp_add]
  have hc30 : (lemma57GaussianLogScale D : ℂ)^2 = (Real.log (D : ℝ) : ℂ)^30 := by
    unfold lemma57GaussianLogScale
    push_cast
    ring
  rw [hc30]

lemma lemma171_log_gaussian_kernel_eq_numerator (D : ℕ) (σ : ℝ) {x : ℝ}
    (hx : 0 < x) (t : ℝ) :
    lemma171LogGaussianKernelIntegrand D σ x t =
      lemma171GaussianNumerator (lemma57GaussianLogScale D) σ (Real.log x) t /
        ((σ : ℂ)+(t : ℂ)*I)^2 := by
  rw [lemma171_gaussian_numerator_eq_cpow D σ hx]
  rfl

lemma lemma171_log_gaussian_kernel_integrable {D : ℕ} (hD : 1 < D)
    {σ x : ℝ} (hσ : σ ≠ 0) (hx : 0 < x) :
    Integrable (lemma171LogGaussianKernelIntegrand D σ x) := by
  have hc : 0 < lemma57GaussianLogScale D :=
    pow_pos (Real.log_pos (by exact_mod_cast hD)) 15
  rw [funext (lemma171_log_gaussian_kernel_eq_numerator D σ hx)]
  exact lemma171_gaussian_second_kernel_integrable hc hσ (Real.log x)

lemma lemma171_vertical_normalization :
    (2*(Real.pi : ℂ)*I)⁻¹*I = (2*(Real.pi : ℂ))⁻¹ := by
  field_simp

lemma lemma171_gaussian_density_normalization {c : ℝ} (hc : 0 < c) (y : ℝ) :
    (2*(Real.pi : ℂ))⁻¹ * (((Real.sqrt Real.pi/c : ℝ) : ℂ) *
      Complex.exp (-(c : ℂ)^2*(y : ℂ)^2)) =
      ((Real.exp (-(c*y)^2)/(2*Real.sqrt Real.pi*c) : ℝ) : ℂ) := by
  have he : Complex.exp (-(c : ℂ)^2*(y : ℂ)^2) =
      ((Real.exp (-(c*y)^2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he]
  have hcoef : (2*(Real.pi : ℂ))⁻¹ * ((Real.sqrt Real.pi/c : ℝ) : ℂ) =
      ((1/(2*Real.sqrt Real.pi*c) : ℝ) : ℂ) := by
    norm_cast
    have hq : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hs := Real.sq_sqrt Real.pi_pos.le
    field_simp [hc.ne', hq.ne', Real.pi_ne_zero]
    nlinarith
  rw [← mul_assoc, hcoef]
  push_cast
  ring

/-- The actual scalar Gaussian inverse Mellin integral with a double pole is
exactly the positive logarithmic Gaussian weight. -/
theorem lemma171LogGaussianKernelVerticalIntegral_eq_weight
    {D : ℕ} (hD : 1 < D) {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    lemma171LogGaussianKernelVerticalIntegral D σ x =
      (lemma171LogGaussianWeight D x : ℂ) := by
  have hc : 0 < lemma57GaussianLogScale D :=
    pow_pos (Real.log_pos (by exact_mod_cast hD)) 15
  have hh := lemma57GaussianKernelVerticalIntegral_eq_weight hD hσ hx
  have heq (t : ℝ) : lemma57GaussianKernelIntegrand D σ x t =
      lemma171GaussianNumerator (lemma57GaussianLogScale D) σ (Real.log x) t /
        ((σ : ℂ)+(t : ℂ)*I) := by
    rw [lemma171_gaussian_numerator_eq_cpow D σ hx]
    rfl
  rw [lemma57GaussianKernelVerticalIntegral, integral_mul_const] at hh
  simp_rw [heq] at hh
  have hH : (2*(Real.pi : ℂ))⁻¹ *
      (∫ t : ℝ, lemma171GaussianNumerator (lemma57GaussianLogScale D) σ (Real.log x) t /
        ((σ : ℂ)+(t : ℂ)*I)) = (zhangGaussianWeight D x : ℂ) := by
    calc
      _ = (2*(Real.pi : ℂ)*I)⁻¹ *
        ((∫ t : ℝ, lemma171GaussianNumerator (lemma57GaussianLogScale D) σ (Real.log x) t /
          ((σ : ℂ)+(t : ℂ)*I))*I) := by rw [← lemma171_vertical_normalization]; ring
      _ = _ := hh
  unfold lemma171LogGaussianKernelVerticalIntegral
  rw [integral_mul_const]
  simp_rw [lemma171_log_gaussian_kernel_eq_numerator D σ hx]
  rw [lemma171_gaussian_second_kernel_integral hc hσ.ne']
  have hn (a : ℂ) : (2*(Real.pi : ℂ)*I)⁻¹*(a*I) = (2*(Real.pi : ℂ))⁻¹*a := by
    rw [← lemma171_vertical_normalization]
    ring
  rw [hn, mul_add]
  rw [show (2*(Real.pi : ℂ))⁻¹ * ((Real.log x : ℂ) *
      (∫ t : ℝ, lemma171GaussianNumerator (lemma57GaussianLogScale D) σ (Real.log x) t /
        ((σ : ℂ)+(t : ℂ)*I))) = (Real.log x : ℂ)*
      ((2*(Real.pi : ℂ))⁻¹ *
      (∫ t : ℝ, lemma171GaussianNumerator (lemma57GaussianLogScale D) σ (Real.log x) t /
        ((σ : ℂ)+(t : ℂ)*I))) by ring,
    hH, lemma171_gaussian_density_normalization hc]
  unfold lemma171LogGaussianWeight
  have hend : zhangGaussianEndpoint D x = lemma57GaussianLogScale D * Real.log x := rfl
  rw [hend]
  push_cast
  rfl

end ZhangLS.Spec
