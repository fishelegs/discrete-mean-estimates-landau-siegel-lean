import FixedQuadratic.ParameterPort.Selection
import FixedQuadratic.ParameterPort.Separation
import FixedQuadratic.AnalysisPort.Packet
import checks.AnalysisRegression

set_option maxHeartbeats 2000000

namespace FixedQuadratic.ParameterPort
open scoped BigOperators
open OAI OAI.PiExponent
open OAI.PiExponent.FixedFieldAnalyticData
open OAI.PiExponent.FixedFieldLiteralAnalytic

/-- Degree-exactly-two approximation in one fixed real field, measured by the
primitive integer minimal polynomial's maximum coefficient height. -/
def exceptionalSet (F : IntermediateField ℚ ℝ) (nu : ℝ) : Set F :=
  {b | (minpoly ℚ (b : ℝ)).natDegree = 2 ∧
    |Real.pi-(b : ℝ)| ≤ (primitiveMinpolyHeight (b : ℝ) : ℝ)^(-nu)}

/-- The same packet is constructed in the order dimension, successive actual
primitive heights, then auxiliary degree. Field degree remains two. -/
theorem fixed_real_quadratic_pi_finite (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) (nu : ℝ) (hnu : 2 < nu) :
    (exceptionalSet F nu).Finite := by
  classical
  by_contra hinf
  have hinf' : (exceptionalSet F nu).Infinite := hinf
  let S : Set ℝ := (fun b : F => (b : ℝ)) '' exceptionalSet F nu
  have hS : S.Infinite := hinf'.image Subtype.val_injective.injOn
  have hdegree : ∀ y ∈ S, (minpoly ℚ y).natDegree = 2 := by
    intro y hy
    obtain ⟨b,hb,rfl⟩ := hy
    exact hb.1
  have hmember : ∀ y ∈ S, y ∈ F := by
    intro y hy
    obtain ⟨b,hb,rfl⟩ := hy
    exact b.property
  obtain ⟨P⟩ := exists_parameters nu hnu
  let g : ℝ := nu*((P.A : ℝ)*(1-P.eta)-P.theta)-(1-P.theta)
  have hg : 0 < g := P.gap_pos
  let epsilon : ℝ := min (g/2) (1/2)
  have heps : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have hepsg : epsilon < g := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hepshalf : epsilon ≤ 1/2 := min_le_right _ _
  have heps3 : 0 < epsilon/3 := by positivity
  obtain ⟨F0,hF0,hFtheta,hFmargin⟩ :=
    exists_initial_scale nu P.theta epsilon P.theta_pos heps
  let c : ℝ := DeterminantContradiction.collisionConstant
  have hc : 0 < c := DeterminantContradiction.collisionConstant_pos
  obtain ⟨m,hm,hdim,hcollision⟩ := FixedQuadratic.exists_changed_dimension_margin
    P.theta P.A P.B P.C P.eta F0 (epsilon/3) (2/c)
    P.theta_pos P.B_pos P.one_lt_C P.CB_lt_one P.one_lt_C_theta_div_B
    P.one_lt_B_div_A P.eta_pos hF0.le heps3
  let K : ℕ := FixedQuadratic.dimensionK P.C m
  let w0 : ℚ := (P.B^m)⁻¹
  let v0 : ℚ := 2*(K : ℚ)*P.theta^m*w0
  have hK : 1 ≤ K := FixedQuadratic.dimensionK_one_le P.C P.one_lt_C.le m
  have hw0eq : (w0 : ℝ) = FixedQuadratic.dimensionW P.B m := by simp [w0,dimensionW]
  have hv0eq : (v0 : ℝ) = FixedQuadratic.dimensionV P.theta P.B P.C m := by
    simp [v0,FixedQuadratic.dimensionV,K,hw0eq]
  have hw0 : 0 < (w0 : ℝ) := by rw [hw0eq]; exact FixedQuadratic.dimensionW_pos P.B P.B_pos m
  have hv0 : 0 < (v0 : ℝ) := by
    rw [hv0eq]
    exact FixedQuadratic.dimensionV_pos P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume : (K : ℝ)*((w0 : ℝ)/v0)*(P.theta : ℝ)^m = 1/2 := by
    rw [hw0eq,hv0eq]
    exact FixedQuadratic.dimension_volume P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume1 : (K : ℝ)*(P.theta : ℝ)^m < 1 :=
    FixedQuadratic.dimension_volume_lt_one P.theta P.C P.theta_pos P.C_pos.le P.C_theta_lt_one m hm
  have hcollision' : 2 < c*(P.eta^2*(K : ℝ)*(P.theta : ℝ)^m/
      (((m : ℝ)+1)*(v0 : ℝ)*(P.A : ℝ)^m)) := by
    rw [hv0eq]
    change 2 < c*(P.eta^2*(FixedQuadratic.dimensionK (P.C : ℝ) m : ℝ)*
      (P.theta : ℝ)^m/(((m : ℝ)+1)*FixedQuadratic.dimensionV P.theta P.B P.C m*(P.A : ℝ)^m))
    rw [FixedQuadratic.dimension_collision_identity P.theta P.A P.B P.C P.eta
      P.theta_pos P.A_pos P.B_pos P.one_lt_C.le]
    have hh := (div_lt_iff₀ hc).mp hcollision
    nlinarith
  obtain ⟨sigma,hsigma,hsigmaVol,hsigmaK,hsigmaTheta⟩ :=
    exists_small_rational_sigma m (1/2) ((K : ℝ)*(P.theta : ℝ)^m) P.theta
      (by norm_num) hvolume1 P.theta_lt_one
  obtain ⟨X,hX,hXmargin⟩ := FixedQuadratic.exists_changed_height_margin nu K (epsilon/3) heps3
  let sep : ℝ := PiExponentApprox.weightSeparationFactor m
    (PersistentWeightComparison.comparisonConstant m sigma) w0 v0 P.theta
  obtain ⟨β,x,hβ,hx0,hxlog,hx1,hxX,hgrowth⟩ := exists_normalized_centers S hS hdegree X sep
  let app : Fin m → F := fun i => ⟨β i.val,hmember _ (hβ i.val).1⟩
  have happeq (i : Fin m) : (app i : ℝ) = β i.val := rfl
  have happ (n : ℕ) : |Real.pi-β n| ≤ (primitiveMinpolyHeight (β n) : ℝ)^(-nu) := by
    obtain ⟨b,hb,he⟩ := (hβ n).1
    simpa only [he] using hb.2
  let d : FixedFieldAnalyticData nu := {
    m := m
    K := K
    K_pos := hK
    F := F
    approximants := app
    degree_two := fun i => hdegree _ (hβ i.val).1
    heights_two_le := fun i => (hβ i.val).2.2
    approximations := fun i => happ i.val
    w0 := w0
    v0 := v0
    theta := P.theta
    A := P.A
    eta := P.eta
    F0 := F0
    wstar := X
    w0_pos := hw0
    v0_pos := hv0
    theta_pos := P.theta_pos
    A_pos := P.A_pos
    eta_pos := P.eta_pos
    F0_pos := hF0
    wstar_pos := zero_lt_one.trans_le hX
    wstar_lower := fun i => by rw [←hxlog]; exact (hxX i.val).le
  }
  have hcast (i : Fin m) : (heightWeightsQ F app i : ℝ) = x (i.val+1) := by
    simp only [heightWeightsQ,Rat.cast_natCast,happeq,←hxlog]
  have hsep := separated_products_from_growth w0 v0 P.theta sigma
    (heightWeightsQ F app) x hw0 hv0 P.theta_pos hsigma hx0 hx1 hcast
    (fun i hi _ => hgrowth i hi)
  have hdim' : (2*formalLcmConstant*F0+3*Real.log 2)/(v0 : ℝ)+
      (100*(K : ℝ)+Real.log (3/2))/(w0 : ℝ) < epsilon/3 := by
    rw [hv0eq,hw0eq]
    exact hdim
  have hheight : heightErrorCoefficient nu K/X < epsilon/3 := hXmargin X le_rfl
  have hsum : FixedQuadratic.arithmeticError F0 v0 w0 X K+d.analyticError < epsilon := by
    have hb := FixedQuadratic.changed_error_lt nu F0 v0 w0 X epsilon K hFmargin hdim' hheight
    have he : d.analyticError = FixedQuadratic.analyticError nu F0 v0 w0 X K := by
      unfold FixedFieldAnalyticData.analyticError FixedFieldAnalyticData.translationError
        FixedFieldAnalyticData.holomorphicError FixedQuadratic.analyticError
      dsimp [d]
      ring
    rw [he]
    exact hb
  apply no_geometric_packet d hF hnu hm sigma hsigma
  · change (1+3*(sigma : ℝ))^(m+1)*((K : ℝ)*((w0 : ℝ)/v0)*(P.theta : ℝ)^m) < 1
    rw [hvolume]
    exact hsigmaVol
  · exact hsigmaK
  · exact hsigmaTheta
  · exact hsep
  · change 1 ≤ F0*(P.theta : ℝ)
    have hh := (div_lt_iff₀ P.theta_pos).mp hFtheta
    linarith
  · change FixedQuadratic.arithmeticError F0 v0 w0 X K+d.analyticError < g
    exact hsum.trans hepsg
  · change 1+FixedQuadratic.arithmeticError F0 v0 w0 X K+d.analyticError <
      c*(P.eta^2*(K : ℝ)*(P.theta : ℝ)^m/(((m : ℝ)+1)*(v0 : ℝ)*(P.A : ℝ)^m))
    linarith

/-- Fully expanded public statement, with no interpolation, norm-integrality,
analytic-bound, parameter-margin or exceptional-set hypothesis. -/
theorem fixed_real_quadratic_pi_finite_explicit (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) (nu : ℝ) (hnu : 2 < nu) :
    Set.Finite {b : F | (minpoly ℚ (b : ℝ)).natDegree = 2 ∧
      |Real.pi-(b : ℝ)| ≤ (primitiveMinpolyHeight (b : ℝ) : ℝ)^(-nu)} :=
  fixed_real_quadratic_pi_finite F hF nu hnu

end FixedQuadratic.ParameterPort
