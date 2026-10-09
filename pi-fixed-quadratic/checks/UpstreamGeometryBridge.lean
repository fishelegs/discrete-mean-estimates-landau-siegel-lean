import FixedQuadratic.FixedFieldArithmetic
import FixedQuadratic.Selection
import OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic
import OAI.NumberTheory.PiExponent.Jets.AdmissibleJetSurjectivity
import OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate

/- The arbitrary-center curve inequality is already a proved upstream theorem.
This bridge instantiates its centers in the actual fixed quadratic field.
It does not assume or assert global interpolation/jet surjectivity. -/
namespace FixedQuadratic.UpstreamGeometry
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.CurveInequality
open OAI.PiExponent.PlaceLocalRing OAI.PiExponent.CurveContactFamily

noncomputable def fixedCenters {m k : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) : Fin k → Fin m → ℂ :=
  fun j i => (j.val : ℂ)*(2*Complex.I*((β i : ℝ) : ℂ))

theorem fixedCenters_injective {m k : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (i : Fin m) : Function.Injective (fun j : Fin k => fixedCenters (k := k) F β j i) :=
  quadratic_centers_injective (β i : ℝ) (degree_two_ne_zero _ (hβ i)) k

/-- A genuine geometric contact inequality for the actual fixed-field centers,
using only the source's explicit geometric weight conditions. -/
theorem fixed_field_weighted_curve_inequality {m k : ℕ}
    (F : IntermediateField ℚ ℝ) (β : Fin m → F)
    (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (k : ℝ)*(1+3*(sigma : ℝ))^(m+1)*
      (∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (hfibrevol : (k : ℝ)*(1+3*(sigma : ℝ))^m*
      (∏ i : Fin m, (w i.succ : ℝ))/(∏ i : Fin m, (v i.succ : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      OAI.PiExponent.PersistentWeightComparison.comparisonConstant m sigma*
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ))*(w i.succ : ℝ) < v i.succ) :
    let hres := OAI.PiExponent.PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := OAI.PiExponent.CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (m+1) → E := Fin.cases y x
    let hz := OAI.PiExponent.CurveInequality.nonconstant_coordinates z hgen htrdeg
    (1+(sigma : ℝ))*∑ p ∈ OAI.PiExponent.CurveContactFamily.places hfinite z (fixedCenters (k := k) F β) hz,
      (OAI.PiExponent.CurveContactFamily.contact hres hfinite z (fixedCenters (k := k) F β) hz v p : ℝ) ≤
        OAI.PiExponent.CurveContactSum.weightedDegree hfinite z w := by
  exact OAI.PiExponent.CurveInequality.weighted_curve_inequality y x (fixedCenters (k := k) F β)
    (fixedCenters_injective (k := k) F β hβ) hgen htrdeg w v hw hv sigma hsigma
    hvol hfibrevol hseparated hratio

end FixedQuadratic.UpstreamGeometry
#check @FixedQuadratic.UpstreamGeometry.fixedCenters
#print axioms FixedQuadratic.UpstreamGeometry.fixedCenters
#check @FixedQuadratic.UpstreamGeometry.fixedCenters_injective
#print axioms FixedQuadratic.UpstreamGeometry.fixedCenters_injective
#check @FixedQuadratic.UpstreamGeometry.fixed_field_weighted_curve_inequality
#print axioms FixedQuadratic.UpstreamGeometry.fixed_field_weighted_curve_inequality

/- Print the exact existing types of the remaining rational-data interfaces.
These are audited dependencies, not new generalized theorems. -/
#check @OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample
#print axioms OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample
#check @OAI.PiExponent.AdmissibleJetSurjectivity.eventually_jetRestriction_surjective
#print axioms OAI.PiExponent.AdmissibleJetSurjectivity.eventually_jetRestriction_surjective
#check @OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound
#print axioms OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound
