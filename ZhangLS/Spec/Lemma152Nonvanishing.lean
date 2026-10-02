import ZhangLS.Spec.Lemma152Repaired
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1000000

lemma lemma152_nonzero_of_small_alpha {D : ℕ} (χ : RealPrimitiveCharacter D) {c : ℝ}
    (hc : 0<c) (hL : 3 ≤ lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (herror : lemma152ErrorConstant*lemma44PaperAlpha D < 1)
    (s : ℂ) (hs : ‖s-1‖ < 5*lemma44PaperAlpha D) :
    lemma152EulerProduct χ (lemma152PaperBeta D c) s ≠ 0 :=
  lemma153_nonzero_of_center_distance_lt_one χ _
    ((lemma152_paper_estimate χ hc hL hsmall s hs).trans_lt herror)

/-- The actual analytic M₁ is nonzero throughout the complete paper disc,
once D is large. No nonzero value is assumed as an input. -/
lemma lemma152_nonvanishing_threshold {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
        lemma152EulerProduct χ (lemma152PaperBeta D c) s ≠ 0 := by
  obtain ⟨D₁,hsection₁,hsmall₁⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨D₂,hsection₂,hsmall₂⟩ := lemma52_exists_shift_threshold lemma152_error_constant_pos
  refine ⟨max 2 (max D₁ D₂),le_max_left _ _,?_⟩
  intro D hD χ s hs
  have hD₁ : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hD₂ : D₂≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hsection₁.trans hD₁)).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hnonneg : 0 ≤ lemma152ErrorConstant*lemma44PaperAlpha D :=
    mul_nonneg lemma152_error_constant_pos.le ha.le
  have herror : lemma152ErrorConstant*lemma44PaperAlpha D < 1 := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ lemma23PaperL D by linarith) hnonneg
    rw [mul_one] at hh
    exact (hh.trans (hsmall₂ D hD₂)).trans_lt (by norm_num)
  exact lemma152_nonzero_of_small_alpha χ hc hL (hsmall₁ D hD₁) herror s hs

end ZhangLS.Spec
