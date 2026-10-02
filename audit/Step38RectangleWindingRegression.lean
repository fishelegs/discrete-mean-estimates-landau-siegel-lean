import ZhangLS.Spec.Lemma57RectangleWinding

/-!
# Step 38 rectangle winding regression

This check pins the orientation, winding integral, and equivalence between the
normalized finite shift and the standard rectangle boundary identity.
-/

namespace ZhangLS.Spec

open Complex

example (T : ℝ) (hT : 0 < T) :
    lemma57RectangleBoundaryIntegral (fun s : ℂ => s⁻¹) T =
      2 * (Real.pi : ℂ) * I :=
  lemma57RectangleBoundaryIntegral_inv T hT

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Lemma57FiniteRectangleShift χ ↔
      ∀ T : ℝ, 0 < T →
        lemma57RectangleBoundaryIntegral (lemma57MellinIntegrand χ) T =
          2 * (Real.pi : ℂ) * I * lemma57ResidueValue χ :=
  lemma57FiniteRectangleShift_iff_boundaryIntegral χ

end ZhangLS.Spec
