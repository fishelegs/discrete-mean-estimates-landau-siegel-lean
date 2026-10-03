import ZhangLS.Spec.AppendixBTailContour

/-! Unconditional original-rectangle deformation for the genuine tail source
integrand, using the frozen auxiliary zeta strip and exact gamma cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex Metric Set Filter
open scoped Topology

theorem appendixB_tail_actual_rectangle_circle :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ β γ : ℂ,
      β.re=0 → ‖β‖≤3*lemma44PaperAlpha D → ‖γ‖≤3*lemma44PaperAlpha D →
      ∀ L z : ℝ, ∀ l₁ : ℕ,
      lemma44GeneralRectangleBoundaryIntegral (lemma151TailIntegrand D L z β γ l₁)
        (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) (proposition71ZetaAuxHeight D/2)=
      circleIntegral (lemma151TailIntegrand D L z β γ l₁) 0 (5*lemma44PaperAlpha D) := by
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
  intro β γ hβre hβ hγ L z l₁
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
  have hraw (s : ℂ) (hs : s∈S) (hs0 : s≠0) (hsb : s≠β) (hsg : s≠γ) :
      appendixBTailContinuedIntegrand D L z β γ l₁ s=lemma151TailIntegrand D L z β γ l₁ s := by
    exact appendixB_tail_continued_agrees D L z β γ l₁ hs0
      (by intro he; have hp := (hpos s hs).1; rw [he] at hp; simp at hp) hsb
      (by intro he; have hp := (hpos s hs).2; rw [he] at hp; simp at hp) hsg
  have hR : 0<5*lemma44PaperAlpha D := by positivity
  have hβR : ‖β‖<5*lemma44PaperAlpha D := by linarith
  have hγR : ‖γ‖<5*lemma44PaperAlpha D := by linarith
  have h0R : ‖(0 : ℂ)‖<5*lemma44PaperAlpha D := by simpa using hR
  have hzero := lemma84_pole_inside_rectangle hgeom.2.1.le hgeom.2.2.1.le hY.le h0R
  have hbeta := lemma84_pole_inside_rectangle hgeom.2.1.le hgeom.2.2.1.le hY.le hβR
  have hgamma := lemma84_pole_inside_rectangle hgeom.2.1.le hgeom.2.2.1.le hY.le hγR
  have hbound : lemma44GeneralRectangleBoundaryIntegral (appendixBTailContinuedIntegrand D L z β γ l₁)
      (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) (proposition71ZetaAuxHeight D/2)=
      lemma44GeneralRectangleBoundaryIntegral (lemma151TailIntegrand D L z β γ l₁)
      (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) (proposition71ZetaAuxHeight D/2) := by
    apply lemma84_boundary_integral_congr (by linarith [hgeom.2.1]) (by positivity [hH1])
    intro s hs
    exact hraw s hs.1 (lemma84_boundary_ne_pole hzero hs)
      (lemma84_boundary_ne_pole hbeta hs) (lemma84_boundary_ne_pole hgamma hs)
  have hcircle : circleIntegral (appendixBTailContinuedIntegrand D L z β γ l₁)
      0 (5*lemma44PaperAlpha D)=
      circleIntegral (lemma151TailIntegrand D L z β γ l₁) 0 (5*lemma44PaperAlpha D) := by
    apply circleIntegral.integral_congr hR.le
    intro s hs
    exact hraw s (lemma84_closedBall_subset_rectangle hgeom.2.1.le hgeom.2.2.1.le hY.le
      (sphere_subset_closedBall hs)) (lemma84_sphere_ne_pole h0R hs)
      (lemma84_sphere_ne_pole hβR hs) (lemma84_sphere_ne_pole hγR hs)
  rw [←hbound,←hcircle]
  exact appendixB_tail_rectangle_circle D L z β γ l₁ hgeom.2.1 hgeom.2.2.1 hY hR hpos hzfree

end ZhangLS.Spec
