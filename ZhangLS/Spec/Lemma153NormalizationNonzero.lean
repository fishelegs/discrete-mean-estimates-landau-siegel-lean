import ZhangLS.Spec.Lemma152Nonvanishing
import ZhangLS.Spec.Lemma153Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1000000

lemma lemma153_paper_beta_norm_le {D : ℕ} {c : ℝ} (hL : 3 ≤ lemma23PaperL D)
    (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10) (j : Fin 3) :
    ‖lemma83PaperBeta D c j‖ ≤ 3*lemma44PaperAlpha D := by
  obtain ⟨h1,h2,h3⟩ := lemma52_offset_bounds hL hc hsmall
  fin_cases j
  · simpa [lemma83PaperBeta,lemma52PaperBetaOne,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg h1.1] using h1.2
  · simpa [lemma83PaperBeta,lemma52PaperBetaTwo,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg h2.1] using h2.2
  · simpa [lemma83PaperBeta,lemma52PaperBetaThree,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg h3.1] using h3.2

/-- The exact M₁ denominator appearing in (15.19) is genuinely nonzero for
all three original shifts and all sufficiently large D, uniformly in χ,j. -/
lemma lemma153_normalization_nonzero_threshold {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ∀ j : Fin 3,
        lemma152EulerProduct χ (lemma152PaperBeta D c) (1-lemma83PaperBeta D c j) ≠ 0 := by
  obtain ⟨D₁,hD₁,hnonzero⟩ := lemma152_nonvanishing_threshold hc
  obtain ⟨D₂,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D hD χ j
  have hD1 : D₁≤D := (le_max_left _ _).trans hD
  have hD2 : D₂≤D := (le_max_right _ _).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD2)).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  apply hnonzero D hD1 χ
  have hb := lemma153_paper_beta_norm_le hL hc (hsmall D hD2) j
  simpa only [sub_sub_cancel_left,norm_neg] using
    hb.trans_lt (by linarith : 3*lemma44PaperAlpha D < 5*lemma44PaperAlpha D)

/-- A nonzero global normal product has no zero local factor. -/
lemma lemma153_prime_factor_nonzero_of_product {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (s : ℂ) (hM : lemma152EulerProduct χ β s ≠ 0)
    (q : Nat.Primes) : lemma152PrimeFactor χ β q s ≠ 0 := by
  intro hq
  apply hM
  exact tprod_of_exists_eq_zero ⟨q,hq⟩

end ZhangLS.Spec
