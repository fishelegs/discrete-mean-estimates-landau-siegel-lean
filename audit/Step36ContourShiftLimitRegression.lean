import ZhangLS.Spec.Lemma57ContourShiftLimit

/-!
# Step 36 contour-shift limit regression

This check pins the passage from finite rectangle identities and horizontal
decay to the exact infinite contour-shift identity.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Filter
open scoped Real Topology

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hleft : Lemma57VerticalIntegrable χ (-(1 : ℝ) / 2))
    (hfinite : Lemma57FiniteRectangleShift χ)
    (hhorizontal : Lemma57HorizontalDecay χ) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_finite_rectangles χ hD
    hleft hfinite hhorizontal

example {D : ℕ} (χ : RealPrimitiveCharacter D) {σ : ℝ}
    (hint : Lemma57VerticalIntegrable χ σ) :
    Tendsto (lemma57TruncatedVerticalIntegral χ σ) atTop
      (nhds (lemma57VerticalIntegral χ σ)) :=
  lemma57TruncatedVerticalIntegral_tendsto χ hint

end ZhangLS.Spec
