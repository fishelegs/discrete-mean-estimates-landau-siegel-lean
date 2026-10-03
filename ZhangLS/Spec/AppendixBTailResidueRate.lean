import ZhangLS.Spec.AppendixBTailSupport
import ZhangLS.Spec.Lemma151LocalResidue
import ZhangLS.Spec.AppendixBKernelOriginalPhases
import ZhangLS.Spec.Section15SmallFactors

/-! Finite-D residue corrections, quantified before passage to the printed
model. No value or rate for the source's unspecified alpha1 is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex

lemma appendixB_tail_zero_numerator_norm (L z : ℝ) {γ : ℂ} (hγ : γ.re=0) :
    ‖lemma151TailNumerator L z γ 0‖≤2 := by
  have he : lemma151TailNumerator L z γ 0=
      exp (γ*((L*(0.504-z) : ℝ) : ℂ))-exp (γ*((L*0.004 : ℝ) : ℂ)) := by
    unfold lemma151TailNumerator
    congr 1 <;> congr 1 <;> push_cast <;> ring
  rw [he]
  exact (norm_sub_le _ _).trans_eq (by
    rw [appendixB_imaginary_exp_norm hγ,appendixB_imaginary_exp_norm hγ]
    norm_num)

lemma appendixB_tail_residue_local_error {D : ℕ} {α : ℝ}
    (hL : 1≤lemma23PaperL D) (hα : 0<α) (hαs : α≤1/100)
    (L z : ℝ) {β γ : ℂ} (hβ : β≠0) (hβn : ‖β‖≤3*α)
    (hγre : γ.re=0) (hγlo : α≤‖γ‖) (hγhi : ‖γ‖≤3*α) :
    ‖lemma151ExactTailResidue D L z β γ-(β/γ)*lemma151TailNumerator L z γ 0‖≤
      240*α := by
  have hβ1 : 1-β≠0 := by
    intro he
    have he' : β=1 := by linear_combination -he
    rw [he',norm_one] at hβn
    linarith
  have hnear : ‖zetaPoleRemoved (1-β)-1‖≤15*α := by
    have hn : ‖(1-β)-1‖=‖β‖ := by rw [show (1-β)-1= -β by ring,norm_neg]
    have hh := section15_zeta_regular_error (z := 1-β) (by rw [hn]; linarith)
    rw [hn] at hh
    linarith
  have hR : ‖zetaPoleRemoved (1-β)-1‖<1 := by linarith
  have hω : ‖lemma57OmegaOne D (-γ)-1‖≤5*α := by
    have hh := section15_omega_small_error hL (z := -γ) (by rw [norm_neg]; linarith)
    rw [norm_neg] at hh
    have hg0 := norm_nonneg γ
    have hsq : ‖γ‖^2≤9*α^2 := by nlinarith
    nlinarith
  have hq : ‖β/γ‖≤3 := by
    rw [norm_div]
    apply (div_le_iff₀ (hα.trans_le hγlo)).mpr
    linarith
  have hn := appendixB_tail_zero_numerator_norm L z hγre
  have he := lemma151_exact_tail_residue_error D L z (γ := γ) hβ hβ1 hR
  apply he.trans
  apply (div_le_iff₀ (by linarith : 0<1-‖zetaPoleRemoved (1-β)-1‖)).mpr
  have hprod : ‖β/γ‖*‖lemma151TailNumerator L z γ 0‖≤6 :=
    (mul_le_mul hq hn (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hsum : ‖lemma57OmegaOne D (-γ)-1‖+‖zetaPoleRemoved (1-β)-1‖≤20*α := by linarith
  have hm := mul_le_mul hprod hsum (by positivity) (by norm_num : (0 : ℝ)≤6)
  have hc := mul_le_mul_of_nonneg_left hnear (show 0≤240*α by positivity)
  nlinarith

/-- Perturbing beta changes only the linear beta/gamma factor. -/
lemma appendixB_tail_model_beta_error {α δ L z : ℝ} (hα : 0<α) (hδ : 0≤δ)
    {β β₀ γ : ℂ} (hγre : γ.re=0) (hγlo : α≤‖γ‖) (hβ : ‖β-β₀‖≤δ) :
    ‖(β/γ)*lemma151TailNumerator L z γ 0-
      (β₀/γ)*lemma151TailNumerator L z γ 0‖≤2*δ/α := by
  rw [show (β/γ)*lemma151TailNumerator L z γ 0-
      (β₀/γ)*lemma151TailNumerator L z γ 0=
      ((β-β₀)/γ)*lemma151TailNumerator L z γ 0 by ring,norm_mul]
  have hq : ‖(β-β₀)/γ‖≤δ/α := by
    rw [norm_div]
    exact div_le_div₀ hδ hβ hα hγlo
  have hn := appendixB_tail_zero_numerator_norm L z hγre
  exact (mul_le_mul hq hn (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The actual finite-D beta perturbation has an explicit c/L^8 rate before
Gaussian and zeta corrections. This is not an invented O(alpha1). -/
theorem appendixB_actual_tail_beta_rate {D : ℕ} {c : ℝ}
    (hc : 0<c) (hL : 0<lemma23PaperL D) (j : Fin 3) (z : ℝ) :
    ‖((lemma83PaperBeta D c j)/(lemma151Beta6 D))*
        lemma151TailNumerator (lemma23PaperL D^9) z (lemma151Beta6 D) 0-
      ((I*((j.val+1 : ℕ) : ℂ)*(lemma44PaperAlpha D : ℂ))/(lemma151Beta6 D))*
        lemma151TailNumerator (lemma23PaperL D^9) z (lemma151Beta6 D) 0‖≤
          10*c*Real.pi*lemma23PaperL D/lemma23PaperL D^9 := by
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity [Real.pi_pos]
  have hg : (lemma151Beta6 D).re=0 := by simp [lemma151Beta6]
  have hlo : lemma44PaperAlpha D≤‖lemma151Beta6 D‖ := by
    change lemma44PaperAlpha D≤‖appendixBOriginalGamma D (0 : Fin 3)‖
    exact appendixB_original_gamma_lower (D := D) (0 : Fin 3) hα
  have hδ : 0≤5*c*lemma44PaperAlpha D^2*lemma23PaperL D := by positivity
  have hh := appendixB_tail_model_beta_error (L := lemma23PaperL D^9) (z := z)
    hα hδ hg hlo (appendixB_original_beta_perturbation hc hL j)
  apply hh.trans_eq
  have ha : lemma44PaperAlpha D=Real.pi/lemma23PaperL D^9 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
  rw [ha]
  field_simp [hL.ne',Real.pi_ne_zero]
  <;> ring

end ZhangLS.Spec
