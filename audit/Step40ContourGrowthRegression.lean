import ZhangLS.Spec.Lemma57ContourGrowth

/-!
# Step 40 contour-growth regression

This check pins Gaussian absorption on the shifted line and horizontal edges,
and the resulting reduction of the exact contour shift to one conventional
vertical-strip growth estimate for the undamped factor.
-/

namespace ZhangLS.Spec

open Complex Filter
open scoped Real Topology

example {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-b * t ^ 2 + A * t)) atTop (nhds 0) :=
  tendsto_exp_neg_mul_sq_add_mul_atTop hb A

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hgrowth : Lemma57StripExponentialGrowth χ) :
    Lemma57VerticalIntegrable χ (-(1 : ℝ) / 2) :=
  lemma57LeftVerticalIntegrable_of_stripExponentialGrowth χ hD hgrowth

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hgrowth : Lemma57StripExponentialGrowth χ) :
    Lemma57HorizontalDecay χ :=
  lemma57HorizontalDecay_of_stripExponentialGrowth χ hD hgrowth

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hgrowth : Lemma57StripExponentialGrowth χ) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_stripExponentialGrowth χ hD hgrowth

end ZhangLS.Spec
