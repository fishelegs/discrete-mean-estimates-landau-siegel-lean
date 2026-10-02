import ZhangLS.Spec.Lemma57CriticalStripGrowth

/-!
# Step 41 critical-strip growth regression

This check pins the unconditional right-half-plane bounds and the reduction of
the full contour-growth input to the genuine critical half-strip.
-/

namespace ZhangLS.Spec

open Complex

example {s : ℂ} (hs : (3 : ℝ) / 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ lemma57ZetaRightHalfBound :=
  riemannZeta_norm_le_rightHalfBound hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ}
    (hs : (3 : ℝ) / 2 ≤ s.re) :
    ‖dirichletLFunction χ s‖ ≤ lemma57DirichletLRightHalfBound χ :=
  dirichletLFunction_norm_le_rightHalfBound χ hs

example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hcritical : Lemma57CriticalStripExponentialGrowth χ) :
    Lemma57StripExponentialGrowth χ :=
  lemma57StripExponentialGrowth_of_critical χ hcritical

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hcritical : Lemma57CriticalStripExponentialGrowth χ) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_criticalStripExponentialGrowth
    χ hD hcritical

end ZhangLS.Spec
