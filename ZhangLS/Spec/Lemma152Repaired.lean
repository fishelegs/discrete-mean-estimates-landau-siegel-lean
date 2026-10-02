import ZhangLS.Spec.Lemma152ActualContinuation
import ZhangLS.Spec.Lemma152ProductComparison
import ZhangLS.Spec.Lemma153MNonzero
import ZhangLS.Spec.Lemma52

/-!
# Lemma15.2: source-repaired explicit error

Original arXiv:2211.02515v1 p.87 states O(α₁), but α₁ has no definition in
the official TeX. This result proves the same actual M₁ and the same prime
product with the explicit error O(α)=O(π(log D)⁻⁹). It does not define α₁.
The original strict disc, every ramification factor and the shared shift
constant c′ are retained. The theorem holds for every fixed c′>0, so it can
be specialized to the constant already used by Lemmas2.3 and5.2.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def lemma152ErrorConstant : ℝ := 11*lemma152UniformVariationConstant

lemma lemma152_error_constant_pos : 0 < lemma152ErrorConstant :=
  mul_pos (by norm_num) lemma152_uniform_variation_constant_pos

lemma lemma152_alpha_le_hundredth {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    lemma44PaperAlpha D ≤ 1/100 := by
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp,div_le_iff₀ (pow_pos (by linarith : 0<lemma23PaperL D) 9)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hL 9
  norm_num at hp
  nlinarith [Real.pi_le_four]

lemma lemma152_paper_beta_norm_le {D : ℕ} {c : ℝ} (hL : 3 ≤ lemma23PaperL D)
    (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10) (i : Fin 2) :
    ‖lemma152PaperBeta D c i‖ ≤ 3*lemma44PaperAlpha D := by
  obtain ⟨h1,h2,h3⟩ := lemma52_offset_bounds hL hc hsmall
  fin_cases i
  · simpa [lemma152PaperBeta,lemma52PaperBetaOne,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg h1.1] using h1.2
  · simpa [lemma152PaperBeta,lemma52PaperBetaTwo,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg h2.1] using h2.2

/-- Explicit quantitative replacement of the paper's undefined O(α₁) term. -/
lemma lemma152_paper_estimate {D : ℕ} (χ : RealPrimitiveCharacter D) {c : ℝ}
    (hc : 0<c) (hL : 3 ≤ lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (s : ℂ) (hs : ‖s-1‖ < 5*lemma44PaperAlpha D) :
    ‖lemma152EulerProduct χ (lemma152PaperBeta D c) s-lemma152MainTerm χ‖ ≤
      lemma152ErrorConstant*lemma44PaperAlpha D := by
  have ha := lemma152_alpha_le_hundredth hL
  have hb (i : Fin 2) := lemma152_paper_beta_norm_le hL hc hsmall i
  have hs1 : ‖s-1‖ ≤ 1/10 := by linarith
  have hsre : 9/10 ≤ s.re := by
    have hr := Complex.abs_re_le_norm (s-1)
    simp only [Complex.sub_re,Complex.one_re] at hr
    have hh := (abs_le.mp (hr.trans hs1)).1
    linarith
  have hh := lemma152_euler_product_comparison χ (lemma152PaperBeta D c)
    (lemma152_beta_re D c) (fun i => by linarith [hb i]) s hsre hs1
  rw [lemma153_zero_center_equals_main] at hh
  apply hh.trans
  unfold lemma152ErrorConstant
  have hC := lemma152_uniform_variation_constant_pos
  nlinarith [hb 0,hb 1]

/-- Repaired original15.2 with an explicit rate, uniform before D,χ,s. -/
def Lemma152RepairedTarget : Prop :=
  ∀ c : ℝ, 0<c → ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      Lemma152Continuation χ (lemma152PaperBeta D c) 1 1
        (lemma152EulerProduct χ (lemma152PaperBeta D c)) ∧
      ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
        ‖lemma152EulerProduct χ (lemma152PaperBeta D c) s-lemma152MainTerm χ‖ ≤
          C*lemma44PaperAlpha D

/-- The same shift convention and exact arithmetic M₁, with repaired O(α). -/
theorem lemma152_repaired_proved : Lemma152RepairedTarget := by
  intro c hc
  obtain ⟨D₀,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨lemma152ErrorConstant,lemma152_error_constant_pos,max 2 D₀,le_max_left _ _,?_⟩
  intro D hD χ
  have hD' : D₀≤D := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD')).1
  exact ⟨lemma152_actual_continuation χ (lemma152PaperBeta D c) (lemma152_beta_re D c),
    fun s hs => lemma152_paper_estimate χ hc hL (hsmall D hD') s hs⟩

/-- It is valid for the particular shared c′ selected earlier in the paper. -/
theorem lemma152_with_shared_shift_constant :
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
      ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
        ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
          Lemma152Continuation χ (lemma152PaperBeta D c) 1 1
            (lemma152EulerProduct χ (lemma152PaperBeta D c)) ∧
          ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
            ‖lemma152EulerProduct χ (lemma152PaperBeta D c) s-lemma152MainTerm χ‖ ≤
              C*lemma44PaperAlpha D := by
  obtain ⟨c,hc,hcompatible,C,hC,D₀,hrest⟩ := lemma52_proved
  exact ⟨c,hc,hcompatible,lemma152_repaired_proved c hc⟩

end ZhangLS.Spec
