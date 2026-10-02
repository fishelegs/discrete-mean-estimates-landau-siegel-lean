import ZhangLS.Spec.Lemma161ActualContinuation
import ZhangLS.Spec.Lemma161ProductComparison
import ZhangLS.Spec.Lemma161Nonvanishing
import ZhangLS.Spec.Lemma52

/-!
# Original Lemma 16.1, arXiv:2211.02515v1 p.92

The proof uses the exact original arithmetic series, its constructed analytic
continuation and the exact exceptional χ(2)=1 normalization. Direct summable
local variation gives O(α), stronger than the stated O(L⁻⁸). The undefined α₁
in Appendix A is not used. The redundant d*l range is retained in the original
wrapper, since M₂*(s) itself is independent of d and l. No assumption (A) is used.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def lemma161AlphaErrorConstant : ℝ := 16*lemma152UniformVariationConstant
noncomputable def lemma161ErrorConstant : ℝ := lemma161AlphaErrorConstant*Real.pi

lemma lemma161_alpha_error_constant_pos : 0 < lemma161AlphaErrorConstant :=
  mul_pos (by norm_num) lemma152_uniform_variation_constant_pos

lemma lemma161_error_constant_pos : 0 < lemma161ErrorConstant :=
  mul_pos lemma161_alpha_error_constant_pos Real.pi_pos

lemma lemma161_alpha_le_hundredth {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    lemma44PaperAlpha D ≤ 1/100 := by
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp,div_le_iff₀ (pow_pos (by linarith : 0 < lemma23PaperL D) 9)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hL 9
  norm_num at hp
  nlinarith [Real.pi_le_four]

lemma lemma161_paper_beta_norm_le {D : ℕ} {c : ℝ} (hL : 3 ≤ lemma23PaperL D)
    (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10) :
    ‖lemma52PaperBetaOne D c‖ ≤ 3*lemma44PaperAlpha D := by
  obtain ⟨h1,h2,h3⟩ := lemma52_offset_bounds hL hc hsmall
  simpa [lemma52PaperBetaOne,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg h1.1] using h1.2

lemma lemma161_paper_beta_re (D : ℕ) (c : ℝ) : (lemma52PaperBetaOne D c).re = 0 := by
  simp [lemma52PaperBetaOne]

/-- Stronger direct O(α) estimate, uniform over D,χ,s with the fixed paper β₁. -/
lemma lemma161_paper_alpha_estimate {D : ℕ} (χ : RealPrimitiveCharacter D) {c : ℝ}
    (hc : 0<c) (hL : 3 ≤ lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (s : ℂ) (hs : ‖s-1‖ < 5*lemma44PaperAlpha D) :
    ‖lemma161Star χ (lemma52PaperBetaOne D c) s-lemma161MainTerm χ‖ ≤
      lemma161AlphaErrorConstant*lemma44PaperAlpha D := by
  have ha := lemma161_alpha_le_hundredth hL
  have hb := lemma161_paper_beta_norm_le hL hc hsmall
  have hs1 : ‖s-1‖ ≤ 1/10 := by linarith
  have hsre : 9/10 ≤ s.re := by
    have hr := Complex.abs_re_le_norm (s-1)
    simp only [Complex.sub_re,Complex.one_re] at hr
    have hh := (abs_le.mp (hr.trans hs1)).1
    linarith
  have hh := lemma161_star_comparison χ (lemma52PaperBetaOne D c)
    (lemma161_paper_beta_re D c) (by linarith) s hsre hs1
  rw [lemma161_zero_center_equals_main] at hh
  apply hh.trans
  unfold lemma161AlphaErrorConstant
  have hC := lemma152_uniform_variation_constant_pos
  nlinarith

/-- Original O(L⁻⁸), without the weaker L⁻⁷ cutoff envelope. -/
lemma lemma161_paper_estimate {D : ℕ} (χ : RealPrimitiveCharacter D) {c : ℝ}
    (hc : 0<c) (hL : 3 ≤ lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (s : ℂ) (hs : ‖s-1‖ < 5*lemma44PaperAlpha D) :
    ‖lemma161Star χ (lemma52PaperBetaOne D c) s-lemma161MainTerm χ‖ ≤
      lemma161ErrorConstant / lemma23PaperL D^8 := by
  apply (lemma161_paper_alpha_estimate χ hc hL hsmall s hs).trans
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hp : lemma23PaperL D^8 ≤ lemma23PaperL D^9 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  unfold lemma161ErrorConstant lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp,← mul_div_assoc]
  exact div_le_div_of_nonneg_left (mul_pos lemma161_alpha_error_constant_pos Real.pi_pos).le
    (pow_pos hL0 8) hp

/-- Faithful original target, including the strict disc, original dl range,
actual Dirichlet bridge, analytic extension and both χ(2) main constants. -/
def Lemma161OriginalTarget : Prop :=
  ∀ c : ℝ, 0<c → ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      Lemma161Continuation χ (lemma52PaperBetaOne D c) 1 1
        (lemma161EulerProduct χ (lemma52PaperBetaOne D c)) ∧
      AnalyticOnNhd ℂ (lemma161Star χ (lemma52PaperBetaOne D c)) {s : ℂ | 9/10<s.re} ∧
      ∀ d l : ℕ, (d*l:ℝ) < lemma23PaperP D * (lemma56PaperT D)^(-2:ℤ) →
        ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
          ‖lemma161Star χ (lemma52PaperBetaOne D c) s-lemma161MainTerm χ‖ ≤
            C / lemma23PaperL D^8

theorem lemma161_original_proved : Lemma161OriginalTarget := by
  intro c hc
  obtain ⟨D₀,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨lemma161ErrorConstant,lemma161_error_constant_pos,max 2 D₀,le_max_left _ _,?_⟩
  intro D hD χ
  have hD' : D₀≤D := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD')).1
  refine ⟨lemma161_actual_continuation χ _ (lemma161_paper_beta_re D c),
    lemma161_star_analytic χ _ (lemma161_paper_beta_re D c),?_⟩
  intro d l hdl s hs
  exact lemma161_paper_estimate χ hc hL (hsmall D hD') s hs

/-- The c′ may be the same compatible constant already fixed by Lemma5.2. -/
theorem lemma161_with_shared_shift_constant :
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
      ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
        ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
          Lemma161Continuation χ (lemma52PaperBetaOne D c) 1 1
            (lemma161EulerProduct χ (lemma52PaperBetaOne D c)) ∧
          AnalyticOnNhd ℂ (lemma161Star χ (lemma52PaperBetaOne D c)) {s : ℂ | 9/10<s.re} ∧
          ∀ d l : ℕ, (d*l:ℝ) < lemma23PaperP D * (lemma56PaperT D)^(-2:ℤ) →
            ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
              ‖lemma161Star χ (lemma52PaperBetaOne D c) s-lemma161MainTerm χ‖ ≤
                C / lemma23PaperL D^8 := by
  obtain ⟨c,hc,hcompatible,C,hC,D₀,hrest⟩ := lemma52_proved
  exact ⟨c,hc,hcompatible,lemma161_original_proved c hc⟩

end ZhangLS.Spec
