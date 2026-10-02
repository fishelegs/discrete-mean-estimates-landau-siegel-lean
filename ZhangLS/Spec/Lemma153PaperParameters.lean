import ZhangLS.Spec.Lemma153EulerProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

/-- All numerical smallness assumptions for the corrected product hold for
exactly the original shared c′ and three βⱼ, beyond one uniform D-threshold. -/
lemma lemma153_small_parameters_threshold {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ j : Fin 3,
      Lemma153SmallParameters (lemma152PaperBeta D c) (lemma83PaperBeta D c j) := by
  obtain ⟨D₁,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  have hC : 0 < 180*lemma152CorrectionConstant :=
    mul_pos (by norm_num) lemma152_correction_constant_pos
  obtain ⟨D₂,hsection₂,hbudget⟩ := lemma52_exists_shift_threshold hC
  refine ⟨max 2 (max D₁ D₂),le_max_left _ _,?_⟩
  intro D hD j
  have hD1 : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hD2 : D₂≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD1)).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  have has := lemma152_alpha_le_hundredth hL
  have hb (i : Fin 2) := lemma152_paper_beta_norm_le hL hc (hsmall D hD1) i
  have hg := lemma153_paper_beta_norm_le hL hc (hsmall D hD1) j
  refine ⟨lemma152_beta_re D c,fun i => ?_,lemma83_beta_re D c j,?_,?_⟩
  · linarith [hb i]
  · linarith
  · have hh := hbudget D hD2
    have hC0 := lemma152_correction_constant_pos
    have hprod : 0 ≤ lemma152CorrectionConstant*lemma44PaperAlpha D := by positivity
    have hprodle := mul_le_mul_of_nonneg_left (show 1 ≤ lemma23PaperL D by linarith) hprod
    rw [mul_one] at hprodle
    have he : 10*lemma152CorrectionConstant*
        (‖lemma152PaperBeta D c 0‖+‖lemma152PaperBeta D c 1‖+‖lemma83PaperBeta D c j‖) ≤
          90*lemma152CorrectionConstant*lemma44PaperAlpha D := by
      nlinarith only [hb 0,hb 1,hg,hC0]
    apply he.trans
    nlinarith only [hh,hprodle]

/-- Analytic/bounded repaired normal product at the original paper shifts.
The actual Dirichlet-series agreement remains a separate required bridge. -/
lemma lemma153_paper_product_analytic_bounded {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ∀ j : Fin 3,
        AnalyticOnNhd ℂ
          (lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j))
          {s : ℂ | 9/10 ≤ s.re} ∧
        ∀ s : ℂ, 9/10 ≤ s.re →
          ‖lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) s‖ ≤
            lemma153DBound D := by
  obtain ⟨D₀,hD0,hpar⟩ := lemma153_small_parameters_threshold hc
  refine ⟨D₀,hD0,?_⟩
  intro D hD χ j
  have hDne : D ≠ 0 := by omega
  refine ⟨?_,?_⟩
  · exact (lemma153_euler_product_analyticOnNhd hDne χ _ _ (hpar D hD j)).mono
      (fun s hs => by dsimp at *; linarith)
  · intro s hs
    exact lemma153_euler_product_norm_bound hDne χ _ _ (hpar D hD j) s (by linarith)

end ZhangLS.Spec
