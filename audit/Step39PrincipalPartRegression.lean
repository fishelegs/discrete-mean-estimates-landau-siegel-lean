import ZhangLS.Spec.Lemma57PrincipalPart

/-!
# Step 39 principal-part regression

This check pins the entire remainder, the zero double-pole contribution, the
exact finite rectangle residue theorem, and the discharged finite-shift
obligation.
-/

namespace ZhangLS.Spec

open Complex

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Differentiable ℂ (lemma57EntireRemainder χ) :=
  lemma57EntireRemainder_differentiable χ hD

example (T : ℝ) (hT : 0 < T) :
    lemma57RectangleBoundaryIntegral (fun s : ℂ => s⁻¹ ^ 2) T = 0 :=
  lemma57RectangleBoundaryIntegral_inv_sq T hT

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (T : ℝ) (hT : 0 < T) :
    lemma57RectangleBoundaryIntegral (lemma57MellinIntegrand χ) T =
      2 * (Real.pi : ℂ) * I * lemma57ResidueValue χ :=
  lemma57RectangleBoundaryIntegral_mellinIntegrand χ hD T hT

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57FiniteRectangleShift χ :=
  lemma57FiniteRectangleShift_proved χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hleft : Lemma57VerticalIntegrable χ (-(1 : ℝ) / 2))
    (hhorizontal : Lemma57HorizontalDecay χ) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_left_integrable_horizontal_decay
    χ hD hleft hhorizontal

end ZhangLS.Spec
