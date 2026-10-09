import FixedQuadratic.AnalysisPort.Remainders
import FixedQuadratic.Comparison
import FixedQuadratic.GeometryPort.FixedCenters

namespace OAI.PiExponent.FixedFieldLiteralAnalytic
open scoped BigOperators Topology
open Filter FixedFieldAnalyticData

/-- Proved geometric existence for the same actual matrix used in both bounds.
The explicit elementary geometry inputs must still be selected from the
exceptional set; no surjectivity or nonzero-minor hypothesis is supplied. -/
theorem cofinal_nonzero_actual_minor {nu : ℝ} (d : FixedFieldAnalyticData nu)
    (hm : 1 ≤ d.m) (sigma : ℚ) (hsigma : 0 < (sigma : ℝ))
    (hvolume : (1+3*(sigma : ℝ))^(d.m+1)*
      ((d.K : ℝ)*((d.w0 : ℝ)/d.v0)*(d.theta : ℝ)^d.m) < 1)
    (hfibre : (1+3*(sigma : ℝ))^d.m*((d.K : ℝ)*(d.theta : ℝ)^d.m) < 1)
    (hratio : (1+(sigma : ℝ))*(d.theta : ℝ) < 1)
    (hsep : ∀ A B : Finset (Fin (d.m+1)), A.card = B.card → ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant d.m sigma*
        (∏ j ∈ B, (FixedQuadratic.geometricJetWeights d.v0 d.theta
          (FixedQuadratic.heightWeightsQ d.F d.approximants) j : ℝ)) <
        ∏ j ∈ A, (FixedQuadratic.geometricDegreeWeights d.w0
          (FixedQuadratic.heightWeightsQ d.F d.approximants) j : ℝ))
    (hscale : 1 ≤ d.F0*(d.theta : ℝ)) (L : ℝ) :
    ∃ H : ℝ, L ≤ H ∧ ∃ selection : Row d H → Column d H,
      Function.Injective selection ∧ (actualMinor d H selection).det ≠ 0 := by
  have hwcast : ∀ i, (FixedQuadratic.heightWeightsQ d.F d.approximants i : ℝ) = weights d i := by
    intro i
    simp only [FixedQuadratic.heightWeightsQ, weights, MatrixArithmetic.logWeights,
      finiteHeights, Rat.cast_natCast]
  have hTail : ∀ i, FixedQuadratic.heightWeightsQ d.F d.approximants i/d.theta ≤
      (tailOrders d i : ℚ)*d.v0 := by
    intro i
    have hbound : weights d i/(d.theta : ℝ) ≤ d.F0*weights d i := by
      apply (div_le_iff₀ d.theta_pos).mpr
      calc
        weights d i = weights d i*1 := by ring
        _ ≤ weights d i*(d.F0*(d.theta : ℝ)) :=
          mul_le_mul_of_nonneg_left hscale (show 0 ≤ weights d i from (fixedWeights_pos d i).le)
        _ = d.F0*weights d i*(d.theta : ℝ) := by ring
    have ht := MatrixTranslationBounds.truncationOrder_budget (F := d.F0)
      (w := weights d i) d.v0_pos
    have ht' : d.F0*weights d i ≤ (d.v0 : ℝ)*(tailOrders d i : ℝ) := ht
    have hr : (FixedQuadratic.heightWeightsQ d.F d.approximants i : ℝ)/(d.theta : ℝ) ≤
        (tailOrders d i : ℝ)*(d.v0 : ℝ) := by
      rw [hwcast]
      exact hbound.trans (by simpa only [mul_comm] using ht')
    exact_mod_cast hr
  have h := FixedQuadratic.fixed_field_cofinal_nonzero_minor nu 1 1 d.F d.approximants
    d.degree_two d.heights_two_le hm d.K d.w0 d.v0 d.theta sigma
    (by exact_mod_cast d.w0_pos) (by exact_mod_cast d.v0_pos)
    (by exact_mod_cast d.theta_pos) hsigma hvolume hfibre hratio hsep
    (tailOrders d) hTail L
  have he : (fun i => (FixedQuadratic.heightWeightsQ d.F d.approximants i : ℝ)) = weights d :=
    funext hwcast
  rw [he] at h
  exact h

/-- A conditional packet contradiction, not the final pi theorem.
All geometric inputs and strict total-error margins are displayed. They are
not asserted to arise from every infinite exceptional set by this lemma. -/
theorem no_compatible_packet {nu : ℝ} (d : FixedFieldAnalyticData nu)
    [FiniteDimensional ℚ d.F] (hF : Module.finrank ℚ d.F = 2) (hnu : 2 < nu)
    (hminor : ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧ ∃ selection : Row d H → Column d H,
      Function.Injective selection ∧ (actualMinor d H selection).det ≠ 0)
    (hgap : FixedQuadratic.arithmeticError d.F0 d.v0 d.w0 d.wstar d.K+d.analyticError <
      nu*((d.A : ℝ)*(1-d.eta)-d.theta)-(1-d.theta))
    (hcollision : 1+FixedQuadratic.arithmeticError d.F0 d.v0 d.w0 d.wstar d.K+
      d.analyticError < collisionLimit d) : False := by
  let E := FixedQuadratic.arithmeticError d.F0 d.v0 d.w0 d.wstar d.K+d.analyticError
  let rem := fun H => arithmeticRemainder d H+analyticRemainder d H
  have hrem : Tendsto rem atTop (𝓝 0) := by
    simpa only [add_zero] using (tendsto_arithmeticRemainder d).add (tendsto_analyticRemainder d)
  have hsmall : ∀ᶠ H : ℝ in atTop,
      E+rem H < nu*((d.A : ℝ)*(1-d.eta)-d.theta)-(1-d.theta) := by
    apply (tendsto_const_nhds.add hrem).eventually (Iio_mem_nhds ?_)
    simpa only [add_zero] using hgap
  have hlarge : ∀ᶠ H : ℝ in atTop, 1+E+rem H < collisionRate d H := by
    have ht : Tendsto (fun H => collisionRate d H-(1+E+rem H)) atTop
        (𝓝 (collisionLimit d-(1+E+0))) :=
      (tendsto_collisionRate d).sub (tendsto_const_nhds.add hrem)
    have hp : 0 < collisionLimit d-(1+E+0) := by dsimp [E]; linarith
    have hh := ht.eventually (Ioi_mem_nhds hp)
    filter_upwards [hh] with H hH
    linarith
  have hall : ∀ᶠ H : ℝ in atTop, ∀ selection : Row d H → Column d H,
      (actualMinor d H selection).det ≠ 0 → False := by
    filter_upwards [hsmall,hlarge,eventually_gt_atTop (0 : ℝ)] with H hs hl hH
    intro selection hne
    have hb := actual_minor_two_sided d hF (by linarith) hH selection hne
    have hm := MatrixArithmetic.meanRowWeight_le_theta (finiteHeights d)
      (finiteHeights_two_le d) (lt_of_lt_of_le Nat.zero_lt_one d.K_pos)
      d.v0_pos d.theta_pos hH
    have hn := MatrixArithmetic.meanRowWeight_nonneg d.K d.v0 d.theta (finiteHeights d) hH.le
    exact FixedQuadratic.comparison_contradiction nu d.theta d.A d.eta
      (actualMean d H) (collisionRate d H)
      (FixedQuadratic.arithmeticError d.F0 d.v0 d.w0 d.wstar d.K)
      d.analyticError (arithmeticRemainder d H) (analyticRemainder d H)
      (Real.log ‖(actualMinor d H selection).det‖/((actualRowCount d H : ℝ)*H))
      (by linarith) hm hb.1 hb.2 (by dsimp [E,rem] at hs; linarith)
      (by dsimp [E,rem] at hl; linarith) hn
  obtain ⟨L,hL⟩ := eventually_atTop.mp hall
  obtain ⟨H,hH,selection,_,hne⟩ := hminor L
  exact hL H hH selection hne

/-- The conditional contradiction now obtains actual nonzero minors from the
proved geometry chain. Only elementary geometry and scalar parameter margins
remain as inputs. This is not an exceptional-set finiteness theorem. -/
theorem no_geometric_packet {nu : ℝ} (d : FixedFieldAnalyticData nu)
    [FiniteDimensional ℚ d.F] (hF : Module.finrank ℚ d.F = 2) (hnu : 2 < nu)
    (hm : 1 ≤ d.m) (sigma : ℚ) (hsigma : 0 < (sigma : ℝ))
    (hvolume : (1+3*(sigma : ℝ))^(d.m+1)*
      ((d.K : ℝ)*((d.w0 : ℝ)/d.v0)*(d.theta : ℝ)^d.m) < 1)
    (hfibre : (1+3*(sigma : ℝ))^d.m*((d.K : ℝ)*(d.theta : ℝ)^d.m) < 1)
    (hratio : (1+(sigma : ℝ))*(d.theta : ℝ) < 1)
    (hsep : ∀ A B : Finset (Fin (d.m+1)), A.card = B.card → ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant d.m sigma*
        (∏ j ∈ B, (FixedQuadratic.geometricJetWeights d.v0 d.theta
          (FixedQuadratic.heightWeightsQ d.F d.approximants) j : ℝ)) <
        ∏ j ∈ A, (FixedQuadratic.geometricDegreeWeights d.w0
          (FixedQuadratic.heightWeightsQ d.F d.approximants) j : ℝ))
    (hscale : 1 ≤ d.F0*(d.theta : ℝ))
    (hgap : FixedQuadratic.arithmeticError d.F0 d.v0 d.w0 d.wstar d.K+d.analyticError <
      nu*((d.A : ℝ)*(1-d.eta)-d.theta)-(1-d.theta))
    (hcollision : 1+FixedQuadratic.arithmeticError d.F0 d.v0 d.w0 d.wstar d.K+
      d.analyticError < collisionLimit d) : False :=
  no_compatible_packet d hF hnu
    (cofinal_nonzero_actual_minor d hm sigma hsigma hvolume hfibre hratio hsep hscale)
    hgap hcollision

end OAI.PiExponent.FixedFieldLiteralAnalytic
