import ZhangLS.Spec.Lemma57GaussianMellinKernel

/-!
# Step 33 scalar Gaussian Mellin-kernel regression

This focused check pins absolute integrability of the scalar kernel, its exact
identification with mathlib's inverse Mellin transform, and the reduction of
kernel evaluation to one explicit `HasMellin` calculation.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

example {D : ℕ} (hD : 1 < D) {σ x : ℝ} (hσ : σ ≠ 0) (hx : 0 < x) :
    Integrable (lemma57GaussianKernelIntegrand D σ x) :=
  lemma57GaussianKernel_integrable hD hσ hx

example (D : ℕ) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    lemma57GaussianKernelVerticalIntegral D σ x =
      mellinInv σ (fun s : ℂ => lemma57OmegaOne D s / s) x⁻¹ :=
  lemma57GaussianKernelVerticalIntegral_eq_mellinInv D σ hx

example {D : ℕ} (hD : 1 < D) {σ : ℝ} (hσ : σ ≠ 0) :
    Complex.VerticalIntegrable (fun s : ℂ => lemma57OmegaOne D s / s) σ :=
  lemma57Omega_div_verticalIntegrable hD hσ

example {D : ℕ} (hD : 1 < D)
    (htransform : Lemma57GaussianKernelTransform D)
    {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    lemma57GaussianKernelVerticalIntegral D σ x =
      (zhangGaussianWeight D x : ℂ) :=
  lemma57GaussianKernelVerticalIntegral_eq_weight_of_transform
    hD htransform hσ hx

end ZhangLS.Spec
