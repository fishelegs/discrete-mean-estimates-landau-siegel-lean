import ZhangLS.Spec.Lemma84ContourGeometry
import ZhangLS.Spec.Lemma84ContourBridge
import ZhangLS.Spec.Lemma84ArithmeticCircle
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric
open scoped Topology
set_option maxHeartbeats 2000000

/-- Exact finite contour transfer for the actual L quotient and actual U.
The proof removes the actual simple exceptional zero and the double smoothing
pole, with all remaining terms genuinely analytic on the full rectangle. -/
lemma lemma84_actual_finite_contour {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) {ρ : ℝ}
    (hρ : 0 < 1-ρ) (hclose : 1-ρ ≤ 64*lemma23PaperL D^(-2022 : ℤ))
    (hzero : dirichletLFunction χ (ρ:ℂ)=0) (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z=0 → z=(ρ:ℂ))
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) {x : ℝ} (hx : 0 < x) :
    let F := lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
      (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ)
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x
    lemma44GeneralRectangleBoundaryIntegral F (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) D =
      circleIntegral F 0 (5*lemma44PaperAlpha D) := by
  dsimp only
  let a := (ρ:ℂ)-1
  let b := -lemma84SmoothingBeta D μ
  let U := lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r
  let N := lemma84ActualTwoPoleNumerator χ ρ (lemma83PaperBeta D c (j+1))
    (lemma83PaperBeta D c (j+2)) U x
  let S := lemma44ClosedRectangle (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) D
  have hgeom := lemma84_paper_rectangle_geometry hD hL
  have ha : ‖a‖ < 5*lemma44PaperAlpha D :=
    (lemma84_exceptional_zero_within_alpha (by linarith only [hL] : 100 ≤ lemma23PaperL D) hρ hclose).trans_lt
      (by linarith only [hgeom.1])
  have hm := lemma84_smoothing_beta_norm μ hgeom.1
  have hb : ‖b‖ < 5*lemma44PaperAlpha D := by
    dsimp [b]
    rw [norm_neg]
    linarith only [hm.2,hgeom.1]
  have hball : closedBall (0:ℂ) (5*lemma44PaperAlpha D) ⊆ S :=
    lemma84_ball_subset_rectangle hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
  have hnhds (w : ℂ) (hw : ‖w‖ < 5*lemma44PaperAlpha D) : S ∈ nhds w :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds (by simpa using hw)) (ball_subset_closedBall.trans hball)
  have hU : AnalyticOnNhd ℂ U {z : ℂ | 9/10 < z.re} :=
    lemma83_euler_correction_analyticOnNhd χ _ (lemma83_beta_re D c) j d r
  have hS : ∀ s ∈ S, 9/10 < (1+s).re ∧ Lemma55InZeroRegion D (1+s) :=
    fun s hs => lemma84_rectangle_inside_analytic_region hD hL hs
  have hN : DifferentiableOn ℂ N S := lemma84_actual_two_pole_numerator_differentiableOn χ hD
    (by linarith only [hρ]) hzero hsimple hunique _ _ U hU hx hS
  have hR := lemma84_two_pole_remainder_differentiableOn N hN a b (hnhds a ha) (hnhds b hb)
  apply lemma84_rectangle_circle_bridge_of_decomposition _ (lemma84TwoPoleRemainder N a b)
    (lemma84TwoPoleCoefficientA N a b) (lemma84TwoPoleCoefficientB N a b)
    (lemma84TwoPoleCoefficientC N a b) hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 ha hb hR
  intro s hs hsa hsb
  exact lemma84_actual_two_pole_decomposition χ (by linarith only [hρ]) hzero hsimple hunique
    (lemma83PaperBeta D c (j+1)) (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ)
    (lemma84_smoothing_beta_re D μ) U x s (hS s hs) hsa hsb

lemma lemma84_actual_normalized_finite_contour {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) {ρ : ℝ}
    (hρ : 0 < 1-ρ) (hclose : 1-ρ ≤ 64*lemma23PaperL D^(-2022 : ℤ))
    (hzero : dirichletLFunction χ (ρ:ℂ)=0) (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z=0 → z=(ρ:ℂ))
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) {x : ℝ} (hx : 0 < x) :
    let F := lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
      (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ)
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x
    (2*Real.pi:ℂ)⁻¹*((∫ t : ℝ in -(D:ℝ)..D, F ((6*lemma44PaperAlpha D:ℝ)+I*(t:ℂ))) -
      (∫ t : ℝ in -(D:ℝ)..D, F ((-1/lemma23PaperL D:ℝ)+I*(t:ℂ)))) +
    (2*Real.pi*I:ℂ)⁻¹*((∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D), F ((σ:ℂ)-I*(D:ℂ))) -
      (∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D), F ((σ:ℂ)+I*(D:ℂ)))) =
      lemma84PaperCircle χ c j μ d r x := by
  dsimp only
  have hh := lemma84_actual_finite_contour χ hD hL hρ hclose hzero hsimple hunique c j μ d r hx
  dsimp only at hh
  unfold lemma44GeneralRectangleBoundaryIntegral at hh
  unfold lemma84PaperCircle
  rw [←hh]
  simp only [Complex.ofReal_natCast,mul_comm (I:ℂ)]
  field_simp
  ring

end ZhangLS.Spec
