import FixedQuadratic.GeometryPort.AdmissibleJetSurjectivity
import FixedQuadratic.GeometryPort.AdmissibleJetPackets
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame
import OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound
import OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity

set_option maxHeartbeats 2000000

namespace OAI
noncomputable section
namespace PiExponent.FixedFieldInterpolation
open AlgebraicGeometry CategoryTheory Filter
open PiExponentSeshadri.Geometry
open FixedFieldBlowupGeometry FixedFieldJetPackets
attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap AffineJetCoefficientInterface.Frame
  AffineJetCoefficientInterface.Sections AffineJetCoefficientInterface.coefficient
variable {ν Λ D : ℝ} (d : FixedFieldGeometryData ν Λ D)

theorem exponent_budget (j : Index d) :
    Finsupp.weight (fun i => (d.curveDegreeWeights i : ℝ)) (exponents d j) ≤ (scale d).radius := by
  have hq := (scale d).budget d.curveDegreeWeights_pos j
  have hr : (∑ i, (d.curveDegreeWeights i : ℝ)*(exponents d j i : ℝ)) ≤ (scale d).radius := by
    exact_mod_cast hq
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hr

theorem eventual_supportBound :
    ProjectiveCoefficientBound.EventualBound (affineChart d) (hyperplane d)
      (fun i => (d.curveDegreeWeights i : ℝ)) (scale d).radius := by
  unfold affineChart hyperplane
  exact WeightedGlobalSectionBound.eventual_supportBound (K := ℂ) (ι := Fin (d.m+1))
    (σ := Index d) (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ)) (scale d).radius (exponent_budget d)

theorem actualFrame_exists :
    Nonempty (AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d)) := by
  exact AdmissibleMatrixInterpolation.monomialFrame_exists (R := ℂ)
    (exponents d) (constantIndex d) ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)

def WeightedPolynomials (n : ℕ) :=
  {P : PiExponentApprox.FramePolynomial d.m // WeightedSliceDegree.SupportBound
    (fun i => (d.curveDegreeWeights i : ℝ)) ((n : ℝ)*(scale d).radius) P}

def packetMap (n : ℕ) (P : WeightedPolynomials d n) := fun j : Fin d.K =>
  JetGeometry.rationalCoefficientPacket d.curveJetWeights ((n : ℚ)*(scale d).radius)
    (FormalLogJet.formalJet (d.curveCenters j) P.val)

theorem packetMap_surjective_of_family {α : Type*} (n : ℕ)
    (P : α → PiExponentApprox.FramePolynomial d.m)
    (hdegree : ∀ a, WeightedSliceDegree.SupportBound
      (fun i => (d.curveDegreeWeights i : ℝ)) ((n : ℝ)*(scale d).radius) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin d.K =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights ((n : ℚ)*(scale d).radius)
        (FormalLogJet.formalJet (d.curveCenters j) (P a)))) :
    Function.Surjective (packetMap d n) := by
  intro y
  obtain ⟨a,ha⟩ := hpacket y
  exact ⟨⟨P a,hdegree a⟩,ha⟩

/-- The actual geometric chain proves packet surjectivity. No surjectivity
hypothesis is assumed here: the proved blowup ampleness supplies it. -/
theorem eventually_packetMap_surjective :
    ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n) := by
  obtain ⟨N,hN⟩ := eventual_supportBound d
  obtain ⟨e⟩ := actualFrame_exists d
  filter_upwards [FixedFieldJetSurjectivity.eventually_jetRestriction_surjective d,
    eventually_ge_atTop N] with n hn hnN
  apply packetMap_surjective_of_family d n (sectionPolynomial d n e)
  · intro s
    exact hN n hnN e s
  · exact formalPackets_surjective_of_jetRestriction d n e hn

/-- Converts the proved geometric packets to the literal truncated-log matrix.
The explicit weight/center identities and tail budget are geometric inputs. -/
theorem actualMatrix_surjective_of_packetMap (n : ℕ)
    (w0 v θ : ℝ) (w : Fin d.m → ℝ) (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (hdegree : ∀ i, (d.curveDegreeWeights i : ℝ) = InterpolationMatrix.columnWeights w0 w i)
    (hrow : ∀ i, (d.curveJetWeights i : ℝ) = InterpolationMatrix.rowWeights v θ w i)
    (r : Fin d.m → ℂ) (hc : ∀ j i, d.curveCenters j i = (j.val : ℂ)*r i)
    (T : Fin d.m → ℕ) (hT : ∀ i, d.curveJetWeights i.succ ≤ (T i : ℚ)*d.curveJetWeights 0)
    (hp : Function.Surjective (packetMap d n)) :
    Function.Surjective (InterpolationMatrix.truncatedLogMatrix d.K w0 v θ w
      ((n : ℝ)*(scale d).radius) r T).mulVecLin := by
  have he : d.curveCenters = fun j i => (j.val : ℂ)*r i := funext (fun j => funext (hc j))
  have hW : (fun i => (d.curveDegreeWeights i : ℝ)) = InterpolationMatrix.columnWeights w0 w :=
    funext hdegree
  have hh := FormalMatrixBridge.truncatedLogMatrix_surjective_of_formalLog_packets
    d.K w0 v θ w ((n : ℚ)*(scale d).radius) hw0 hw
    d.curveJetWeights d.curveJetWeights_pos hrow r T hT
    (fun P : WeightedPolynomials d n => P.val) (fun P => ?_) (by
      change Function.Surjective (fun P : WeightedPolynomials d n => fun j : Fin d.K =>
        JetGeometry.rationalCoefficientPacket d.curveJetWeights ((n : ℚ)*(scale d).radius)
          (FormalLogJet.formalJet (d.curveCenters j) P.val)) at hp
      simp_rw [he] at hp
      exact hp)
  · have hcast : (((n : ℚ)*(scale d).radius : ℚ) : ℝ) = (n : ℝ)*(scale d).radius := by push_cast; rfl
    exact hcast ▸ hh
  · intro a ha
    have h := P.property a ha
    rw [hW] at h
    simpa only [PiExponentApprox.monomialWeight, Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_mul, Rat.cast_natCast] using h

/-- Arbitrarily large actual matrix degrees have full row rank, as a conclusion
of the complete curve/ample/jet chain. -/
theorem cofinal_actualMatrix_surjective
    (w0 v θ : ℝ) (w : Fin d.m → ℝ) (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (hdegree : ∀ i, (d.curveDegreeWeights i : ℝ) = InterpolationMatrix.columnWeights w0 w i)
    (hrow : ∀ i, (d.curveJetWeights i : ℝ) = InterpolationMatrix.rowWeights v θ w i)
    (r : Fin d.m → ℂ) (hc : ∀ j i, d.curveCenters j i = (j.val : ℂ)*r i)
    (T : Fin d.m → ℕ) (hT : ∀ i, d.curveJetWeights i.succ ≤ (T i : ℚ)*d.curveJetWeights 0)
    (L : ℝ) : ∃ H : ℝ, L ≤ H ∧ Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix d.K w0 v θ w H r T).mulVecLin := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_packetMap_surjective d)
  let n := max N (Nat.ceil (L/((scale d).radius : ℝ)))
  have hR : (0 : ℝ) < (scale d).radius := by exact_mod_cast (scale d).radius_pos
  have hL : L ≤ (n : ℝ)*(scale d).radius := by
    apply (div_le_iff₀ hR).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right N (Nat.ceil (L/((scale d).radius : ℝ)))))
  exact ⟨(n : ℝ)*(scale d).radius,hL,
    actualMatrix_surjective_of_packetMap d n w0 v θ w hw0 hw hdegree hrow r hc T hT
      (hN n (le_max_left _ _))⟩

/-- Actual nonzero full-row minor existence, derived rather than assumed. -/
theorem cofinal_nonzero_full_row_minor
    (w0 v θ : ℝ) (w : Fin d.m → ℝ) (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (hdegree : ∀ i, (d.curveDegreeWeights i : ℝ) = InterpolationMatrix.columnWeights w0 w i)
    (hrow : ∀ i, (d.curveJetWeights i : ℝ) = InterpolationMatrix.rowWeights v θ w i)
    (r : Fin d.m → ℂ) (hc : ∀ j i, d.curveCenters j i = (j.val : ℂ)*r i)
    (T : Fin d.m → ℕ) (hT : ∀ i, d.curveJetWeights i.succ ≤ (T i : ℚ)*d.curveJetWeights 0)
    (L : ℝ) : ∃ H : ℝ, L ≤ H ∧ ∃ selection : InterpolationMatrix.Row d.K v θ w H →
      InterpolationMatrix.Column w0 w H, Function.Injective selection ∧
      ((InterpolationMatrix.truncatedLogMatrix d.K w0 v θ w H r T).submatrix id selection).det ≠ 0 := by
  classical
  obtain ⟨H,hH,hs⟩ := cofinal_actualMatrix_surjective d w0 v θ w hw0 hw hdegree hrow r hc T hT L
  obtain ⟨p,hp,hdet⟩ := InterpolationMatrix.exists_full_row_minor_of_surjective _ hs
  exact ⟨H,hH,p,hp,hdet⟩

end PiExponent.FixedFieldInterpolation
end
end OAI
