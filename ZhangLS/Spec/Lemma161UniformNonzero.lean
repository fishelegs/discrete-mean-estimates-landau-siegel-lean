import ZhangLS.Spec.Lemma161Original

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1200000

lemma lemma161_star_norm_lower_of_small {D : ℕ} (χ : RealPrimitiveCharacter D) {c : ℝ}
    (hc : 0<c) (hL : 3 ≤ lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (herror : lemma161AlphaErrorConstant*lemma44PaperAlpha D ≤ lemma161MainLowerBound/2)
    (s : ℂ) (hs : ‖s-1‖ < 5*lemma44PaperAlpha D) :
    lemma161MainLowerBound/2 ≤ ‖lemma161Star χ (lemma52PaperBetaOne D c) s‖ := by
  have he := lemma161_paper_alpha_estimate χ hc hL hsmall s hs
  have hl := lemma161_main_norm_lower χ
  have hn := norm_le_norm_sub_add (lemma161MainTerm χ) (lemma161Star χ (lemma52PaperBetaOne D c) s)
  rw [norm_sub_rev] at hn
  linarith

/-- The paper's post-Lemma16.1 conclusion |M₂*(s)| ≫ 1, with a positive
constant independent of D, χ, s, and of the exceptional χ(2) case. -/
theorem lemma161_uniform_nonzero :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
        ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
          lemma161MainLowerBound/2 ≤ ‖lemma161Star χ (lemma52PaperBetaOne D c) s‖ := by
  intro c hc
  obtain ⟨D₁,hsection,hshift⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨D₂,hsection₂,hsmall⟩ := lemma46_exists_contraction_threshold
    (div_pos lemma161_alpha_error_constant_pos lemma161_main_lower_bound_pos)
  refine ⟨max 2 (max D₁ D₂),le_max_left _ _,?_⟩
  intro D hD χ s hs
  have hD₁ : D₁≤D := (le_max_left D₁ D₂).trans ((le_max_right 2 _).trans hD)
  have hD₂ : D₂≤D := (le_max_right D₁ D₂).trans ((le_max_right 2 _).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD₁)).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hsmall' := hsmall D hD₂
  have hratio : (lemma161AlphaErrorConstant/lemma161MainLowerBound)*lemma44PaperAlpha D ≤ 1/2 := by
    have hmul : (lemma161AlphaErrorConstant/lemma161MainLowerBound)*lemma44PaperAlpha D ≤
        (lemma161AlphaErrorConstant/lemma161MainLowerBound)*lemma44PaperAlpha D*lemma23PaperL D := by
      apply le_mul_of_one_le_right
      · exact mul_nonneg (div_pos lemma161_alpha_error_constant_pos lemma161_main_lower_bound_pos).le ha.le
      · linarith
    exact hmul.trans hsmall'
  have herror : lemma161AlphaErrorConstant*lemma44PaperAlpha D ≤ lemma161MainLowerBound/2 := by
    have hh := mul_le_mul_of_nonneg_right hratio lemma161_main_lower_bound_pos.le
    have he : (lemma161AlphaErrorConstant/lemma161MainLowerBound)*lemma44PaperAlpha D*
        lemma161MainLowerBound = lemma161AlphaErrorConstant*lemma44PaperAlpha D := by
      field_simp [ne_of_gt lemma161_main_lower_bound_pos]
    rw [he] at hh
    linarith
  exact lemma161_star_norm_lower_of_small χ hc hL (hshift D hD₁) herror s hs

lemma lemma161_star_ne_zero_eventually :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
        ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
          lemma161Star χ (lemma52PaperBetaOne D c) s ≠ 0 := by
  intro c hc
  obtain ⟨D₀,hD₀,h⟩ := lemma161_uniform_nonzero c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ s hs he
  have hh := h D hD χ s hs
  rw [he,norm_zero] at hh
  have hp := lemma161_main_lower_bound_pos
  linarith

end ZhangLS.Spec
