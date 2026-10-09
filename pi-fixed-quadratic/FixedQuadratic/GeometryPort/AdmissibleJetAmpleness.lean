import FixedQuadratic.GeometryPort.AdmissibleBlowupAmple
import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity

/- Adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Ampleness/AdmissibleJetAmpleness.lean, Apache-2.0. Generalized geometry inputs; proof chain preserved. -/

namespace OAI

namespace PiExponent.FixedFieldJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.FixedFieldBlowupGeometry PiExponent.BlowupJetSurjectivity
attribute [local irreducible] FixedFieldBlowupGeometry.centerIdeal
  FixedFieldBlowupGeometry.hyperplane
variable {ν Λ D : ℝ} (d : FixedFieldGeometryData ν Λ D)

theorem blowupBundle_ample :
    (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple := by
  apply PiExponent.AmpleIso.isAmple_of_sheaf_iso (interpolationBundle d)
    (blowupBundle (centerIdeal d) (hyperplane d))
    (moduleTensorComm (A d).sheaf (J d).sheaf)
  exact interpolationBundle_ample d

end
end PiExponent.FixedFieldJetSurjectivity

end OAI
