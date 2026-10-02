import ZhangLS.Spec.Lemma56MarginLogDerivative
import ZhangLS.Spec.Lemma53GaussianInverse

/-! # Actual Gaussian inverse Mellin kernel at every positive scale

The kernel is evaluated using the proved scalar inverse Mellin formula.
No smoothed arithmetic sum is defined by its desired integral value.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000

noncomputable def lemma56GaussianOmega (B : ℝ) (s : ℂ) : ℂ :=
  ((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp (s ^ 2 / (4 * (B : ℂ) ^ 2))

noncomputable def lemma56GaussianWeight (B x : ℝ) : ℝ :=
  Real.exp (-(B ^ 2 * (Real.log x) ^ 2))

noncomputable def lemma56GaussianKernel (B σ x t : ℝ) : ℂ :=
  (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) *
    lemma56GaussianOmega B ((σ : ℂ) + (t : ℂ) * I)

lemma lemma56_gaussian_kernel_reciprocal {B σ x t : ℝ} (hx : 0 < x) :
    lemma56GaussianKernel B σ x t =
      ((x⁻¹ : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) *
        (((Real.sqrt Real.pi / B : ℝ) : ℂ) *
          Complex.exp ((((σ : ℂ) + (t : ℂ) * I) - 0) ^ 2 / (4 * (B : ℂ) ^ 2))) := by
  unfold lemma56GaussianKernel lemma56GaussianOmega
  simp only [sub_zero]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (inv_pos.mpr hx).ne'),
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log (inv_pos.mpr hx).le, Real.log_inv]
  push_cast
  congr 1
  ring

theorem lemma56_gaussian_kernel_integrable {B : ℝ} (hB : 0 < B)
    (σ : ℝ) {x : ℝ} (hx : 0 < x) : Integrable (lemma56GaussianKernel B σ x) := by
  have hi := lemma53_gaussian_inverse_integrable hB (0 : ℂ) σ (inv_pos.mpr hx)
  simpa only [← lemma56_gaussian_kernel_reciprocal hx] using hi

theorem lemma56_gaussian_kernel_integral {B : ℝ} (hB : 0 < B)
    (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56GaussianKernel B σ x t =
      (lemma56GaussianWeight B x : ℂ) := by
  have hi := lemma53_gaussian_inverse hB (0 : ℂ) σ (inv_pos.mpr hx)
  unfold mellinInv at hi
  simp only [smul_eq_mul, Complex.real_smul] at hi
  simp_rw [← lemma56_gaussian_kernel_reciprocal hx] at hi
  rw [Real.log_inv] at hi
  have he : Complex.exp (-((B : ℂ) ^ 2 * (Real.log x : ℂ) ^ 2)) =
      (lemma56GaussianWeight B x : ℂ) := by
    unfold lemma56GaussianWeight
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  have hi' : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56GaussianKernel B σ x t =
      Complex.exp (-((B : ℂ) ^ 2 * (Real.log x : ℂ) ^ 2)) := by
    convert hi using 1
    congr 1
    push_cast
    ring
  exact hi'.trans he

theorem lemma56_gaussian_weight_bounds (B x : ℝ) :
    0 < lemma56GaussianWeight B x ∧ lemma56GaussianWeight B x ≤ 1 := by
  unfold lemma56GaussianWeight
  exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg (sq_nonneg B) (sq_nonneg (Real.log x))))⟩

theorem lemma56_gaussian_weight_center (B : ℝ) : lemma56GaussianWeight B 1 = 1 := by
  simp [lemma56GaussianWeight]

end ZhangLS.Spec
