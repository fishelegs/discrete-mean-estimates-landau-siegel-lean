import ZhangLS.Spec.Lemma57GaussianMellinTransform

/-!
# Step 34 Gaussian Mellin-transform regression

This check pins the explicit `HasMellin` evaluation and the resulting
unconditional scalar inverse-Mellin formula.
-/

namespace ZhangLS.Spec

open Complex

example {D : ℕ} (hD : 1 < D) :
    Lemma57GaussianKernelTransform D :=
  lemma57GaussianKernelTransform_proved hD

example {D : ℕ} (hD : 1 < D) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (lemma57ReciprocalGaussianWeight D) s
      (lemma57OmegaOne D s / s) :=
  lemma57GaussianKernelTransform_proved hD s hs

example {D : ℕ} (hD : 1 < D) {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    lemma57GaussianKernelVerticalIntegral D σ x =
      (zhangGaussianWeight D x : ℂ) :=
  lemma57GaussianKernelVerticalIntegral_eq_weight hD hσ hx

end ZhangLS.Spec
