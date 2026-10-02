import ZhangLS.Spec.Lemma57SmoothedSummability

/-!
# Step 30 Gaussian-closure regression

This module pins the public theorem interfaces introduced in Step 29.  Compiling
it checks both the full Gaussian proof chain and the exact terminal APIs consumed
by the Lemma 5.7 reconstruction.
-/

namespace ZhangLS.Spec

example {D : ℕ} (hD : 1 < D) : ZhangGaussianCubicDecay D :=
  zhangGaussianCubicDecay_proved hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57FullSmoothedSummable χ (zhangGaussianWeight D) :=
  lemma57FullSmoothedSummable_proved χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (1 : ℝ) / 8 * lemma57Scale D ≤
      lemma57FullSmoothedSum χ (zhangGaussianWeight D) :=
  lemma57_full_gaussian_arithmetic_scale_proved χ hD

end ZhangLS.Spec
