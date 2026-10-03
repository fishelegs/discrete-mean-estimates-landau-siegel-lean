import ZhangLS.Spec.AppendixBKernelZetaCircle
import ZhangLS.Spec.Lemma84TwoPoleRemoval
import ZhangLS.Spec.Lemma84ContourBridge
import ZhangLS.Spec.Lemma84ContourGeometry

/-! Exact unconditional rectangle-to-circle deformation. The denominator pole
at s=β is analytically continued with (s−β)/Rζ(1+s−β), never ζ(1)⁻¹. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex Metric Set Filter
open scoped Topology

noncomputable def appendixBRegularNumerator (x : ℝ) (β s : ℂ) : ℂ :=
  zetaPoleRemoved (1+s)*(s-β)/zetaPoleRemoved (1+s-β)*(x : ℂ)^s
noncomputable def appendixBRegularIntegrand (x : ℝ) (β γ s : ℂ) : ℂ :=
  appendixBRegularNumerator x β s/(s*(s-γ)^2)

lemma appendixB_regular_integrand_agrees {x : ℝ} {β γ s : ℂ}
    (hs : s≠0) (hs1 : 1+s≠0) (hsb : s≠β) (hsb1 : 1+s-β≠0) :
    appendixBRegularIntegrand x β γ s=appendixBZetaIntegrand x β γ s := by
  unfold appendixBRegularIntegrand appendixBRegularNumerator appendixBZetaIntegrand
  rw [appendixB_zeta_ratio_regularized hs hs1 hsb hsb1]
  simp only [div_eq_mul_inv,mul_inv]
  ring

lemma appendixB_regular_numerator_differentiableOn {x : ℝ} (hx : 0<x)
    (β : ℂ) (S : Set ℂ)
    (hpos : ∀ s∈S, 0<(1+s).re ∧ 0<(1+s-β).re)
    (hfree : ∀ s∈S, zetaPoleRemoved (1+s-β)≠0) :
    DifferentiableOn ℂ (appendixBRegularNumerator x β) S := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  unfold appendixBRegularNumerator
  have h₁ := (lemma55_actual_zeta_pole_removed_analyticAt (hpos s hs).1).differentiableAt
  have h₂ := (lemma55_actual_zeta_pole_removed_analyticAt (hpos s hs).2).differentiableAt
  have hc₁ : DifferentiableAt ℂ (fun z : ℂ => zetaPoleRemoved (1+z)) s :=
    h₁.comp s (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1+z) s)
  have hc₂ : DifferentiableAt ℂ (fun z : ℂ => zetaPoleRemoved (1+z-β)) s :=
    DifferentiableAt.comp s (g := zetaPoleRemoved) (f := fun z : ℂ => 1+z-β) h₂ (by fun_prop)
  exact ((hc₁.mul (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z-β) s)).div
    hc₂ (hfree s hs)).mul
      (Complex.hasStrictDerivAt_const_cpow (y := s)
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).hasDerivAt.differentiableAt

lemma appendixB_regular_rectangle_circle {x a b Y R : ℝ} (hx : 0<x)
    (β γ : ℂ) (hγ : γ≠0)
    (ha : R< -a) (hb : R<b) (hY : R<Y) (hR : 0<R) (hγR : ‖γ‖<R)
    (hpos : ∀ s∈lemma44ClosedRectangle a b Y, 0<(1+s).re ∧ 0<(1+s-β).re)
    (hfree : ∀ s∈lemma44ClosedRectangle a b Y, zetaPoleRemoved (1+s-β)≠0) :
    lemma44GeneralRectangleBoundaryIntegral (appendixBRegularIntegrand x β γ) a b Y =
      circleIntegral (appendixBRegularIntegrand x β γ) 0 R := by
  let N := appendixBRegularNumerator x β
  let S := lemma44ClosedRectangle a b Y
  have hN := appendixB_regular_numerator_differentiableOn hx β S hpos hfree
  have hball : closedBall (0 : ℂ) R⊆S := lemma84_closedBall_subset_rectangle ha.le hb.le hY.le
  have hnhds (w : ℂ) (hw : ‖w‖<R) : S∈𝓝 w :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds (by simpa using hw)) (ball_subset_closedBall.trans hball)
  have hrem := lemma84_two_pole_remainder_differentiableOn N hN 0 γ
    (hnhds 0 (by simpa using hR)) (hnhds γ hγR)
  apply lemma84_rectangle_circle_bridge_of_decomposition (w₁ := (0 : ℂ)) (w₂ := γ) _ (lemma84TwoPoleRemainder N 0 γ)
    (lemma84TwoPoleCoefficientA N 0 γ) (lemma84TwoPoleCoefficientB N 0 γ)
    (lemma84TwoPoleCoefficientC N 0 γ) ha hb hY (by simpa using hR) hγR hrem
  intro s _ hs hsg
  simpa only [appendixBRegularIntegrand,N,sub_zero] using
    lemma84_two_pole_decomposition N 0 γ s (Ne.symm hγ) hs hsg

/-- One unconditional threshold for every actual pure-imaginary β and γ in
3α. The auxiliary height is Y=exp(L^(1/10))/2, distinct from the phase bound. -/
theorem appendixB_actual_rectangle_circle :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ β γ : ℂ,
      β.re=0 → ‖β‖≤3*lemma44PaperAlpha D →
      γ≠0 → ‖γ‖≤3*lemma44PaperAlpha D → ∀ x : ℝ, 0<x →
      lemma44GeneralRectangleBoundaryIntegral (appendixBZetaIntegrand x β γ)
        (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) (proposition71ZetaAuxHeight D/2) =
      circleIntegral (appendixBZetaIntegrand x β γ) 0 (5*lemma44PaperAlpha D) := by
  obtain ⟨N,hN,hstrip⟩ := proposition71_zeta_auxiliary_strip
  have hlog : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (2000 : ℝ)))
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD
  have hL := hM D ((le_max_right _ _).trans hD)
  have hD2 : 1<D := by have := hN.trans ((le_max_left _ _).trans hD); omega
  have hgeom := lemma84_paper_rectangle_geometry hD2 hL
  have hαs := lemma83_alpha_small (by linarith only [hL] : 100≤lemma23PaperL D)
  have hα := hαs.1
  have hH1 : 1≤proposition71ZetaAuxHeight D :=
    Real.one_le_exp (Real.rpow_nonneg (by change 0≤lemma23PaperL D; linarith) _)
  have hY : 5*lemma44PaperAlpha D<proposition71ZetaAuxHeight D/2 := by linarith [hαs.2]
  have hhalf : 1/lemma23PaperL D≤1/2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hfree := (hstrip D ((le_max_left _ _).trans hD)).2.2
  refine ⟨hL,?_⟩
  intro β γ hβre hβ hγ0 hγ x hx
  let S := lemma44ClosedRectangle (-1/lemma23PaperL D) (6*lemma44PaperAlpha D)
    (proposition71ZetaAuxHeight D/2)
  have hpos (s : ℂ) (hs : s∈S) : 0<(1+s).re ∧ 0<(1+s-β).re := by
    have hlo := hs.1.1
    simp only [neg_div] at hlo
    simp only [add_re,one_re,sub_re,hβre,sub_zero]
    constructor <;> linarith
  have hzfree (s : ℂ) (hs : s∈S) : zetaPoleRemoved (1+s-β)≠0 := by
    apply (hfree (1+s-β) ?_ ?_ ?_).1
    · have hlo := hs.1.1
      simp only [neg_div] at hlo
      simp only [add_re,one_re,sub_re,hβre,sub_zero]
      change 1-1/lemma23PaperL D≤1+s.re
      linarith
    · have hhi := hs.1.2
      simp only [add_re,one_re,sub_re,hβre,sub_zero]
      linarith [hαs.2]
    · have ht : |s.im|≤proposition71ZetaAuxHeight D/2 := abs_le.mpr hs.2
      have hbim : |β.im|≤3*lemma44PaperAlpha D := (Complex.abs_im_le_norm β).trans hβ
      simp only [sub_im,add_im,one_im,zero_add]
      have hh : |s.im-β.im|≤|s.im|+|β.im| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le s.im (-β.im)
      exact hh.trans (by linarith [hαs.2])
  have hraw (s : ℂ) (hs : s∈S) (hs0 : s≠0) (hsb : s≠β) :
      appendixBRegularIntegrand x β γ s=appendixBZetaIntegrand x β γ s := by
    exact appendixB_regular_integrand_agrees hs0
      (by intro he; have hp := (hpos s hs).1; rw [he] at hp; simp at hp) hsb
      (by intro he; have hp := (hpos s hs).2; rw [he] at hp; simp at hp)
  have hR : 0<5*lemma44PaperAlpha D := by positivity
  have hβR : ‖β‖<5*lemma44PaperAlpha D := by linarith
  have hγR : ‖γ‖<5*lemma44PaperAlpha D := by linarith
  have h0R : ‖(0 : ℂ)‖<5*lemma44PaperAlpha D := by simpa using hR
  have hzero := lemma84_pole_inside_rectangle hgeom.2.1.le hgeom.2.2.1.le hY.le h0R
  have hbeta := lemma84_pole_inside_rectangle hgeom.2.1.le hgeom.2.2.1.le hY.le hβR
  have hbound : lemma44GeneralRectangleBoundaryIntegral (appendixBRegularIntegrand x β γ)
      (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) (proposition71ZetaAuxHeight D/2) =
      lemma44GeneralRectangleBoundaryIntegral (appendixBZetaIntegrand x β γ)
      (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) (proposition71ZetaAuxHeight D/2) := by
    apply lemma84_boundary_integral_congr (by linarith [hgeom.2.1]) (by positivity [hH1])
    intro s hs
    exact hraw s hs.1 (lemma84_boundary_ne_pole hzero hs) (lemma84_boundary_ne_pole hbeta hs)
  have hcircle : circleIntegral (appendixBRegularIntegrand x β γ) 0 (5*lemma44PaperAlpha D) =
      circleIntegral (appendixBZetaIntegrand x β γ) 0 (5*lemma44PaperAlpha D) := by
    apply circleIntegral.integral_congr hR.le
    intro s hs
    exact hraw s (lemma84_closedBall_subset_rectangle hgeom.2.1.le hgeom.2.2.1.le hY.le
      (sphere_subset_closedBall hs)) (lemma84_sphere_ne_pole h0R hs) (lemma84_sphere_ne_pole hβR hs)
  rw [←hbound,←hcircle]
  exact appendixB_regular_rectangle_circle hx β γ hγ0 hgeom.2.1 hgeom.2.2.1 hY hR hγR hpos hzfree

end ZhangLS.Spec
