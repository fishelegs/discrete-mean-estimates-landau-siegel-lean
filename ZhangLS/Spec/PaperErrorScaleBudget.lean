import ZhangLS.Spec.Lemma44LongSum
import ZhangLS.Spec.Lemma56
import ZhangLS.Spec.Lemma171ResidueBound

/-! Quantitative error-budget identities. These do not assign a definition to the
paper's unexplained alpha-one symbol, nor prove any original numbered estimate. -/
set_option autoImplicit false
namespace ZhangLS.Spec

lemma paper_logT_div_logP {D : ℕ} (hL : 0 < lemma23PaperL D) :
    Real.log (lemma56PaperT D) / Real.log (lemma23PaperP D) =
      lemma23PaperL D ^ (-79 / 10 : ℝ) := by
  rw [lemma56PaperT, lemma23PaperP, Real.log_exp, Real.log_exp]
  rw [← Real.rpow_natCast (lemma23PaperL D) 9, ← Real.rpow_sub hL]
  norm_num

lemma paper_alpha_logT {D : ℕ} (hL : 0 < lemma23PaperL D) :
    lemma44PaperAlpha D * Real.log (lemma56PaperT D) =
      Real.pi * lemma23PaperL D ^ (-79 / 10 : ℝ) := by
  rw [lemma44PaperAlpha]
  calc
    _ = Real.pi * (Real.log (lemma56PaperT D) / Real.log (lemma23PaperP D)) := by ring
    _ = _ := by rw [paper_logT_div_logP hL]

lemma paper_boundary_scale_le_L7 {D : ℕ} (hL : 1 ≤ lemma23PaperL D) :
    Real.log (lemma56PaperT D) / Real.log (lemma23PaperP D) ≤
      lemma23PaperL D ^ (-7 : ℤ) := by
  rw [paper_logT_div_logP (by linarith)]
  rw [← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le hL
  norm_num

lemma paper_alpha_eq_L9 (D : ℕ) :
    lemma44PaperAlpha D = Real.pi * lemma23PaperL D ^ (-9 : ℤ) := by
  rw [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
  simp [zpow_neg, zpow_ofNat, div_eq_mul_inv]

lemma paper_actual_LDeriv_error_budget {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2 ≤ lemma23PaperL D) {C : ℝ}
    {e : ℂ} (he : ‖e‖ ≤ C * lemma44PaperAlpha D) :
    ‖LDerivAtOne χ ^ 2 * e‖ ≤
      ((16 * Real.exp 1)^2 * C * Real.pi) * lemma23PaperL D ^ (-5 : ℤ) := by
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hd : ‖LDerivAtOne χ‖ ≤ 16 * Real.exp 1 * lemma23PaperL D ^ 2 :=
    lemma32_actual_first_derivative_bound χ hD hL (by simp; positivity)
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (16 * Real.exp 1 * lemma23PaperL D ^ 2)^2 *
        (C * lemma44PaperAlpha D) := by gcongr
    _ = ((16 * Real.exp 1)^2 * C * Real.pi) * lemma23PaperL D ^ (-5 : ℤ) := by
      rw [paper_alpha_eq_L9]
      simp only [zpow_neg, zpow_ofNat]
      field_simp

lemma paper_actual_LDeriv_boundary_budget {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2 ≤ lemma23PaperL D) {C : ℝ} (hC : 0 ≤ C)
    {e : ℂ} (he : ‖e‖ ≤ C * (Real.log (lemma56PaperT D) / Real.log (lemma23PaperP D))) :
    ‖LDerivAtOne χ ^ 2 * e‖ ≤
      ((16 * Real.exp 1)^2 * C) * lemma23PaperL D ^ (-3 : ℤ) := by
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hd : ‖LDerivAtOne χ‖ ≤ 16 * Real.exp 1 * lemma23PaperL D ^ 2 :=
    lemma32_actual_first_derivative_bound χ hD hL (by simp; positivity)
  have hscale := paper_boundary_scale_le_L7 (by linarith : 1 ≤ lemma23PaperL D)
  have he' : ‖e‖ ≤ C * lemma23PaperL D ^ (-7 : ℤ) :=
    he.trans (mul_le_mul_of_nonneg_left hscale hC)
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (16 * Real.exp 1 * lemma23PaperL D ^ 2)^2 *
        (C * lemma23PaperL D ^ (-7 : ℤ)) := by gcongr
    _ = ((16 * Real.exp 1)^2 * C) * lemma23PaperL D ^ (-3 : ℤ) := by
      simp only [zpow_neg, zpow_ofNat]
      field_simp

end ZhangLS.Spec
