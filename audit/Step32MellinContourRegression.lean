import ZhangLS.Spec.Lemma57MellinContour

/-!
# Step 32 Mellin/contour regression

This focused kernel check locks down the exact source-level Gaussian Mellin
factor, the Euler--Mascheroni contribution to the residue, the explicit
integrability obligations, and the final `1/16` transfer surface.
-/

namespace ZhangLS.Spec

open Complex

example {D : ℕ} (hD : 1 < D) (s : ℂ) :
    lemma57GaussianMellinFactor D s =
      (D : ℂ) ^ (4 * s) * lemma57OmegaOne D s :=
  lemma57GaussianMellinFactor_eq_cpow_mul_omegaOne hD s

example :
    HasDerivAt lemma57RegularizedZeta
      (Real.eulerMascheroniConstant : ℂ) 0 :=
  lemma57RegularizedZeta_hasDerivAt_zero

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    HasDerivAt (lemma57ResidueNumerator χ) (lemma57ResidueValue χ) 0 :=
  lemma57ResidueNumerator_hasDerivAt_zero χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma57ResidueNumerator χ 0 = LAtOne χ :=
  lemma57ResidueNumerator_zero χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * dirichletLFunction χ s =
      LSeries (divisorCharacterSum χ) s :=
  lemma57DirichletProduct_eq_divisorCharacterLSeries χ hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : s ≠ 0) :
    lemma57MellinIntegrand χ s = lemma57ResidueNumerator χ s / s ^ 2 :=
  lemma57MellinIntegrand_eq_residueNumerator_div_sq χ hs

example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (h : Lemma57MellinIdentity χ) : Lemma57VerticalIntegrable χ 1 :=
  h.1

example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (h : Lemma57ContourShiftIdentity χ) :
    Lemma57VerticalIntegrable χ (-(1 : ℝ) / 2) :=
  h.1

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hmellin : Lemma57MellinIdentity χ)
    (hshift : Lemma57ContourShiftIdentity χ)
    (herror : Lemma57GaussianAnalyticErrorBound χ) :
    (1 : ℝ) / 16 * lemma57Scale D ≤ realLDerivAtOne χ :=
  lemma57_gaussian_mellin_contour_transfer χ hD hmellin hshift herror

end ZhangLS.Spec
