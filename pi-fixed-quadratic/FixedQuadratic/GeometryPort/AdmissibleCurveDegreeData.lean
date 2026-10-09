import FixedQuadratic.GeometryPort.AdmissibleCurveModelDegrees

/- Adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Geometry/AdmissibleCurveDegreeData.lean, Apache-2.0. Generalized geometry inputs; proof chain preserved. -/

namespace OAI

noncomputable section
namespace PiExponent.FixedFieldBlowupMargin
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FixedFieldBlowupGeometry CurveNormalizationModel
variable {ν Λ D : ℝ} (d : FixedFieldGeometryData ν Λ D)

theorem affineCurveDegreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (AffineCurveDegreeData d C) := by
  obtain ⟨r⟩ := FixedFieldCurveModel.existsModelData d C hn hm
  exact ⟨FixedFieldCurveModel.degreeData d C r⟩

end PiExponent.FixedFieldBlowupMargin

namespace PiExponent.FixedFieldBlowupGeometry
open AlgebraicGeometry
variable {ν Λ D : ℝ} (d : FixedFieldGeometryData ν Λ D)

theorem uniform_curve_margin :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  uniform_curve_margin_of_affine_curve_data d (FixedFieldBlowupMargin.affineCurveDegreeData d)

end PiExponent.FixedFieldBlowupGeometry

end

end OAI
