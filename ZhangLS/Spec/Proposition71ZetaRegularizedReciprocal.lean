import ZhangLS.Spec.Proposition71ZetaPaperStrip

/-! # The genuine analytic reciprocal at the zeta pole

Mathlib totalizes ζ(1). The analytic reciprocal needed inside a contour is
therefore (s−1)/Rζ(s), and it agrees with the original boundary reciprocal
away from s=1. Its actual value at the pole is zero.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2500000

noncomputable def proposition71RegularizedZetaReciprocal (s : ℂ) : ℂ :=
  (s-1)/zetaPoleRemoved s

lemma proposition71_regularized_zeta_reciprocal_at_one :
    proposition71RegularizedZetaReciprocal 1=0 := by
  simp [proposition71RegularizedZetaReciprocal]

lemma proposition71_regularized_zeta_reciprocal_eq {s : ℂ} (hs0 : s≠0) (hs1 : s≠1) :
    proposition71RegularizedZetaReciprocal s=(riemannZeta s)⁻¹ := by
  unfold proposition71RegularizedZetaReciprocal
  rw [zetaPoleRemoved_eq_mul_riemannZeta hs0 hs1]
  rw [div_mul_eq_div_div,div_self (sub_ne_zero.mpr hs1),one_div]

lemma proposition71_regularized_zeta_reciprocal_analytic {s : ℂ}
    (hs : 0<s.re) (hne : zetaPoleRemoved s≠0) :
    AnalyticAt ℂ proposition71RegularizedZetaReciprocal s := by
  exact (analyticAt_id.sub analyticAt_const).div
    (lemma55_actual_zeta_pole_removed_analyticAt hs) hne

/-- A true analytic reciprocal, including s=1, with the original α and a
uniform polynomial bound throughout the repaired closed rectangle. -/
theorem proposition71_regularized_zeta_reciprocal_strip :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      3≤lemma23PaperL D ∧ ∀ z : ℂ, 1-1/lemma23PaperL D≤z.re →
        z.re≤1+lemma44PaperAlpha D → |z.im|≤proposition71ZetaAuxHeight D →
        AnalyticAt ℂ proposition71RegularizedZetaReciprocal z ∧
          ‖proposition71RegularizedZetaReciprocal z‖≤9*Real.exp 1*lemma23PaperL D^17 := by
  obtain ⟨D₁,hD₁,hpaper⟩ := proposition71_zeta_paper_strip_bounds
  obtain ⟨D₂,hD₂,hstrip⟩ := proposition71_zeta_auxiliary_strip
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D hD
  obtain ⟨hL,hbound⟩ := hpaper D ((le_max_left _ _).trans hD)
  have hstripD := (hstrip D ((le_max_right _ _).trans hD)).2.2
  refine ⟨hL,?_⟩
  intro z hzlo hzhi hzt
  have hLp : 0<lemma23PaperL D := by linarith
  have hhalf : 1/lemma23PaperL D≤1/2 := by
    apply (div_le_div_iff₀ hLp (by norm_num : (0 : ℝ)<2)).mpr
    linarith
  have hα := (proposition71_zeta_paper_alpha_budget hL).2.1
  have hzpos : 0<z.re := by linarith
  have hR := (hstripD z hzlo (by linarith : z.re≤2) hzt).1
  refine ⟨proposition71_regularized_zeta_reciprocal_analytic hzpos hR,?_⟩
  by_cases hz1 : z=1
  · subst z
    rw [proposition71_regularized_zeta_reciprocal_at_one,norm_zero]
    positivity
  · have hz0 : z≠0 := by intro hh; rw [hh] at hzpos; simp at hzpos
    rw [proposition71_regularized_zeta_reciprocal_eq hz0 hz1]
    exact (hbound z hz1 hzlo hzhi hzt).2.1

end ZhangLS.Spec
