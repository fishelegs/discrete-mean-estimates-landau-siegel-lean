import ZhangLS.Spec.Lemma162CenterComparison
import ZhangLS.Spec.Lemma162PaperArithmeticBridge

/-! The printed positive Euler expression is the center main term of the
corrected V, with a finite-shift error. The old ζ³L³ quotient has center zero
and is not reintroduced anywhere in this comparison. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

/-- Literal positive Euler expression, with the original two-branch mathfrak p. -/
noncomputable def lemma162CorrectedCenterMain {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  (6/(Real.pi:ℂ)^2)*((Nat.totient D:ℂ)/((D:ℂ)*lemma161MainTerm χ))*
    ∏ q ∈ D.primeFactors, (q:ℂ)/((q:ℂ)+1)

lemma lemma162_corrected_center_main_eq {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma162CorrectedCenterMain χ = lemma162RawEulerProduct χ 0 0 1/lemma161MainTerm χ := by
  rw [lemma162_raw_center_zero_exact,lemma171_correction_at_one]
  unfold lemma162CorrectedCenterMain
  push_cast
  ring

noncomputable def lemma162CorrectedCenterVariationConstant : ℝ :=
  2*lemma162CenterVariationConstant/lemma161MainLowerBound+
    4*lemma152UniformVariationConstant/lemma161MainLowerBound^2

lemma lemma162_corrected_center_variation_constant_pos : 0<lemma162CorrectedCenterVariationConstant := by
  unfold lemma162CorrectedCenterVariationConstant
  have h1 := lemma162_center_variation_constant_pos
  have h2 := lemma152_uniform_variation_constant_pos
  have h3 := lemma161_main_lower_bound_pos
  positivity

/-- The denominator bound is a quantitative hypothesis here, discharged for
both original paper shifts in the eventual theorem below. -/
lemma lemma162_corrected_center_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (hbsmall : ‖β‖≤1/10)
    (γ : ℂ) (hγ : γ.re=0) (hgsmall : ‖γ‖≤1/10)
    (hA : lemma161MainLowerBound/2≤‖lemma161Star χ β (1-γ)‖) :
    ‖lemma162CorrectedEulerProduct χ β γ 1-lemma162CorrectedCenterMain χ‖≤
      lemma162CorrectedCenterVariationConstant*(‖β‖+‖γ‖) := by
  let R := lemma162RawEulerProduct χ β γ 1
  let R₀ := lemma162RawEulerProduct χ 0 0 1
  let A := lemma161Star χ β (1-γ)
  let p := lemma161MainTerm χ
  let E := ‖β‖+‖γ‖
  have hE : 0≤E := by dsimp [E]; positivity
  have hL := lemma161_main_lower_bound_pos
  have hP : lemma161MainLowerBound≤‖p‖ := lemma161_main_norm_lower χ
  have hAn : A≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hA)
  have hPn : p≠0 := norm_pos_iff.mp (hL.trans_le hP)
  have hR := lemma162_raw_center_product_comparison χ β hβ hbsmall γ hγ hgsmall
  have hR₀ := lemma162_raw_center_zero_norm_le_one χ
  have hs : 9/10≤(1-γ).re := by simp [hγ]; norm_num
  have hdist : ‖(1-γ)-1‖=‖γ‖ := by rw [show (1-γ)-1 = -γ by ring,norm_neg]
  have hAp := lemma161_star_comparison χ β hβ hbsmall (1-γ) hs (by rwa [hdist])
  rw [lemma161_zero_center_equals_main,hdist] at hAp
  rw [lemma162CorrectedEulerProduct,lemma162_corrected_center_main_eq]
  change ‖R/A-R₀/p‖≤_
  rw [show R/A-R₀/p = (R-R₀)/A+R₀*(p-A)/(A*p) by field_simp; ring]
  apply (norm_add_le _ _).trans
  rw [norm_div,norm_div,norm_mul,norm_mul,norm_sub_rev p A]
  have hden : lemma161MainLowerBound^2/2≤‖A‖*‖p‖ := by
    have hh := mul_le_mul hA hP hL.le (norm_nonneg A)
    nlinarith
  have ht1 : ‖R-R₀‖/‖A‖≤(lemma162CenterVariationConstant*E)/(lemma161MainLowerBound/2) :=
    div_le_div₀ (mul_nonneg lemma162_center_variation_constant_pos.le hE) hR
      (by linarith) hA
  have hnum : ‖R₀‖*‖A-p‖≤(2*lemma152UniformVariationConstant)*E := by
    calc
      _ ≤ 1*((2*lemma152UniformVariationConstant)*E) :=
        mul_le_mul hR₀ hAp (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have ht2 : ‖R₀‖*‖A-p‖/(‖A‖*‖p‖)≤
      ((2*lemma152UniformVariationConstant)*E)/(lemma161MainLowerBound^2/2) :=
    div_le_div₀ (by have := lemma152_uniform_variation_constant_pos; positivity) hnum
      (by positivity) hden
  apply (add_le_add ht1 ht2).trans
  unfold lemma162CorrectedCenterVariationConstant
  dsimp [E]
  apply le_of_eq
  field_simp
  ring

noncomputable def lemma162CorrectedCenterAlphaConstant : ℝ :=
  6*lemma162CorrectedCenterVariationConstant

lemma lemma162_corrected_center_alpha_constant_pos : 0<lemma162CorrectedCenterAlphaConstant :=
  mul_pos (by norm_num) lemma162_corrected_center_variation_constant_pos

/-- Finite-D β₁ and β₂, same fixed c′, absolute O(α) error. No assumption(A)
or existence of an(A)-character is used. -/
theorem lemma162_paper_corrected_center_alpha (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
        ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c)
          (lemma162PaperShift D c j) 1-lemma162CorrectedCenterMain χ‖≤
            lemma162CorrectedCenterAlphaConstant*lemma44PaperAlpha D := by
  obtain ⟨D₁,hD₁,hstar⟩ := lemma161_uniform_nonzero c hc
  obtain ⟨D₂,hsection,hshift⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max 3 (max D₁ D₂),le_max_left _ _,hsection.trans
    ((le_max_right D₁ D₂).trans (le_max_right 3 _)),?_⟩
  intro D hD χ j
  have h1 : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have h2 : D₂≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans h2)).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hasmall := lemma161_alpha_le_hundredth hL
  have hb := lemma161_paper_beta_norm_le hL hc (hshift D h2)
  have hg : ‖lemma162PaperShift D c j‖≤3*lemma44PaperAlpha D :=
    lemma83_paper_beta_norm hL hc (hshift D h2) _
  have hdist : ‖(1-lemma162PaperShift D c j)-1‖<5*lemma44PaperAlpha D := by
    rw [show (1-lemma162PaperShift D c j)-1 = -lemma162PaperShift D c j by ring,norm_neg]
    linarith
  have hN := hstar D h1 χ _ hdist
  have hh := lemma162_corrected_center_comparison χ _ (lemma161_paper_beta_re D c)
    (by linarith) _ (lemma162_paper_shift_re D c j) (by linarith) hN
  apply hh.trans
  unfold lemma162CorrectedCenterAlphaConstant
  calc
    _ ≤ lemma162CorrectedCenterVariationConstant*(6*lemma44PaperAlpha D) :=
      mul_le_mul_of_nonneg_left (by linarith only [hb,hg]) lemma162_corrected_center_variation_constant_pos.le
    _ = _ := by ring

/-- The source's O(L⁻⁴) center error holds for the corrected V; the theorem
actually retains the stronger L⁻⁹ rate, with explicit constant. -/
theorem lemma162_paper_corrected_center (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
        ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c)
          (lemma162PaperShift D c j) 1-lemma162CorrectedCenterMain χ‖≤
            (lemma162CorrectedCenterAlphaConstant*Real.pi)/lemma23PaperL D^9 := by
  obtain ⟨D₀,hD₀,hsection,h⟩ := lemma162_paper_corrected_center_alpha c hc
  refine ⟨D₀,hD₀,hsection,?_⟩
  intro D hD χ j
  have hh := h D hD χ j
  simpa only [lemma44PaperAlpha,lemma23PaperP,Real.log_exp,mul_div_assoc] using hh

end ZhangLS.Spec
