import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem
import FixedQuadratic.GeometryPort.AdmissibleCurveDegreeData

/- Adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Ampleness/AdmissibleBlowupAmple.lean, Apache-2.0. Generalized geometry inputs; proof chain preserved. -/

namespace OAI

noncomputable section
namespace PiExponent.FixedFieldBlowupGeometry
variable {ν Λ D : ℝ} (d : FixedFieldGeometryData ν Λ D)

theorem interpolationBundle_ample : (interpolationBundle d).IsAmple :=
  NumericalAmpleness.isAmple_of_uniform_curve_margin (structureMap d)
    (H d) (interpolationBundle d) (H_ample d) (uniformMargin d)
    (uniformMargin_pos d) (uniform_curve_margin d)

end PiExponent.FixedFieldBlowupGeometry

end

end OAI
