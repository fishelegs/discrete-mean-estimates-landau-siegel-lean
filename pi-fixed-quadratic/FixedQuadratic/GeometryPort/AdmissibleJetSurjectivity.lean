import FixedQuadratic.GeometryPort.AdmissibleJetAmpleness
import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete

/- Adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Jets/AdmissibleJetSurjectivity.lean, Apache-2.0. Generalized geometry inputs; proof chain preserved. -/

namespace OAI

namespace PiExponent.FixedFieldJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.FixedFieldBlowupGeometry PiExponent.BlowupJetSurjectivity
attribute [local irreducible] FixedFieldBlowupGeometry.centerIdeal
  FixedFieldBlowupGeometry.hyperplane
variable {ν Λ D : ℝ} (d : FixedFieldGeometryData ν Λ D)

theorem eventual_jetRestriction_surjective :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  exact eventual_blowup_jetRestriction_surjective
    (compactificationStructureMap d) (centerIdeal d) (hyperplane d) (blowupBundle_ample d)

theorem eventually_jetRestriction_surjective :
    ∀ᶠ n in Filter.atTop, Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  obtain ⟨N,hN⟩ := eventual_jetRestriction_surjective d
  exact Filter.eventually_atTop.mpr ⟨N,hN⟩

end
end PiExponent.FixedFieldJetSurjectivity

end OAI
