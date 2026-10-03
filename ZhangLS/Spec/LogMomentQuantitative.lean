import ZhangLS.Spec.LogGaussianUnsmoothing
import ZhangLS.Spec.LogContourInfinite
import ZhangLS.Spec.LogResidueMain
import ZhangLS.Spec.Lemma171MainLowerBound

/-! Quantitative assembly from the genuine contour, residue, and weighted series. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex

noncomputable def lemma171HarmonicErrorBudget (D : ℕ) : ℝ :=
  (1 + lemma44InverseSquareMass) * lemma23PaperL D ^ (-180 : ℤ) +
    1260 * lemma23PaperL D ^ (-2011 : ℤ) + (D : ℝ) ^ (-4 : ℤ) +
    lemma171ResidueErrorConstant * lemma23PaperL D ^ (-2018 : ℤ) + lemma171LeftMajorant D

lemma lemma171_actual_harmonic_error_quantitative {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    (hT : 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D)) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D ^ (-2013 : ℤ)) :
    |lemma171ShortHarmonicSum χ - lemma171MainTerm χ| ≤ lemma171HarmonicErrorBudget D := by
  have hu := lemma171_unsmoothing_bound χ hD hL hT hA hAbs
  have hr := lemma171_actual_residue_error_bound χ hD (by linarith) hA
  have hl := lemma171_left_vertical_norm_le_majorant χ hD
  have hs := lemma171_smoothed_sum_eq_residue_add_left χ hD
  have he : (lemma171ShortHarmonicSum χ : ℂ) - (lemma171MainTerm χ : ℂ) =
      ((lemma171ShortHarmonicSum χ - lemma171SmoothedSum χ : ℝ) : ℂ) +
        (lemma171ActualResidue χ - (lemma171MainTerm χ : ℂ)) + lemma171VerticalIntegral χ (-1/4) := by
    push_cast
    rw [hs]
    ring
  calc
    _ = ‖(lemma171ShortHarmonicSum χ : ℂ) - (lemma171MainTerm χ : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖((lemma171ShortHarmonicSum χ - lemma171SmoothedSum χ : ℝ) : ℂ)‖ +
        ‖lemma171ActualResidue χ - (lemma171MainTerm χ : ℂ)‖ +
        ‖lemma171VerticalIntegral χ (-1/4)‖ := by rw [he]; exact norm_add₃_le
    _ ≤ _ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      unfold lemma171HarmonicErrorBudget
      linarith

lemma lemma171_log_smoothed_sum_eq_residue_add_left {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (lemma171LogSmoothedSum χ : ℂ) =
      lemma171ActualLogResidue χ + lemma171LogVerticalIntegral χ (-1/4) := by
  rw [← (lemma171_log_gaussian_mellin_identity χ hD).2]
  exact lemma171_log_actual_infinite_contour_shift χ hD

noncomputable def lemma171FirstLogMomentError {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  lemma171FirstLogMoment χ + lemma171MainTerm χ *
    (2 * lemma171RealSecondJet χ / realLDerivAtOne χ +
      2 * Real.eulerMascheroniConstant + lemma171CorrectionLogDerivative D)

noncomputable def lemma171FirstLogMomentBudget (D : ℕ) : ℝ :=
  (1 + lemma44InverseSquareMass) * lemma23PaperL D ^ (-180 : ℤ) +
    2520 * lemma23PaperL D ^ (-2002 : ℤ) + lemma23PaperL D ^ 9 * (D : ℝ) ^ (-4 : ℤ) +
    lemma171LogResidueErrorConstant * lemma23PaperL D ^ (-2016 : ℤ) +
    4 * lemma171LeftMajorant D + lemma23PaperL D ^ 9 * lemma171HarmonicErrorBudget D

lemma lemma171_actual_first_log_moment_error_quantitative {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    (hT : 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D)) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D ^ (-2013 : ℤ))
    (hd : realLDerivAtOne χ ≠ 0) :
    |lemma171FirstLogMomentError χ| ≤ lemma171FirstLogMomentBudget D := by
  have hu := lemma171_log_unsmoothing_bound χ hD hL hT hA hAbs
  have hr := lemma171_actual_log_residue_error_bound χ hD (by linarith) hA
  have hl := lemma171_log_left_vertical_norm_le_majorant χ hD
  have hs := lemma171_log_smoothed_sum_eq_residue_add_left χ hD
  have hmain := lemma171_log_residue_main_re χ hD hd
  have hOld := lemma171_actual_harmonic_error_quantitative χ hD hL hT hA hAbs
  have hL0 : 0 ≤ lemma23PaperL D := by linarith only [hL]
  have hT0 : 0 ≤ Real.log (lemma56PaperT D) := by linarith
  have hT9 := lemma171_log_T_le (D := D) (by linarith)
  have hsre := congrArg Complex.re hs
  simp only [Complex.ofReal_re, Complex.add_re] at hsre
  have he : lemma171FirstLogMomentError χ =
      (lemma171LogSmoothedSum χ -
        (Real.log (lemma56PaperT D) * lemma171ShortHarmonicSum χ - lemma171FirstLogMoment χ)) -
      (lemma171ActualLogResidue χ - lemma171LogResidueMain χ).re -
      (lemma171LogVerticalIntegral χ (-1/4)).re +
      Real.log (lemma56PaperT D) * (lemma171ShortHarmonicSum χ - lemma171MainTerm χ) := by
    unfold lemma171FirstLogMomentError
    rw [Complex.sub_re, hmain]
    linear_combination -hsre
  have hre := (Complex.abs_re_le_norm (lemma171ActualLogResidue χ - lemma171LogResidueMain χ)).trans hr
  have hle := (Complex.abs_re_le_norm (lemma171LogVerticalIntegral χ (-1/4))).trans hl
  have hprod : |Real.log (lemma56PaperT D) * (lemma171ShortHarmonicSum χ - lemma171MainTerm χ)| ≤
      lemma23PaperL D ^ 9 * lemma171HarmonicErrorBudget D := by
    rw [abs_mul, abs_of_nonneg hT0]
    exact mul_le_mul hT9 hOld (abs_nonneg _) (by positivity)
  rw [he]
  calc
    _ ≤ |lemma171LogSmoothedSum χ -
        (Real.log (lemma56PaperT D) * lemma171ShortHarmonicSum χ - lemma171FirstLogMoment χ)| +
        |(lemma171ActualLogResidue χ - lemma171LogResidueMain χ).re| +
        |(lemma171LogVerticalIntegral χ (-1/4)).re| +
        |Real.log (lemma56PaperT D) * (lemma171ShortHarmonicSum χ - lemma171MainTerm χ)| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ _ := by unfold lemma171FirstLogMomentBudget; linarith

end ZhangLS.Spec
