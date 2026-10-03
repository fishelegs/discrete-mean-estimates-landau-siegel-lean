import ZhangLS.Spec.LogResidueBudget
import ZhangLS.Spec.RealAxisHigherDerivatives
import ZhangLS.Spec.CorrectionLogReality

/-! Exact source normalization of the logarithmic residue's main term. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Metric Set Filter
open scoped Topology

noncomputable def lemma171RealSecondJet {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  (iteratedDeriv 2 (dirichletLFunction χ) 1).re / 2

lemma lemma171_second_jet_is_actual {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    iteratedDeriv 2 (dirichletLFunction χ) 1 / 2 = (lemma171RealSecondJet χ : ℂ) :=
  dirichletLFunction_second_jet_at_one_eq_ofReal χ hD

lemma lemma171_regular_zeta_hasDerivAt_zero :
    HasDerivAt (fun w : ℂ => zetaPoleRemoved (1+w)) (Real.eulerMascheroniConstant : ℂ) 0 := by
  apply lemma57RegularizedZeta_hasDerivAt_zero.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1/4)] with w hw
  have hn : ‖w‖ < 1/4 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  by_cases hw0 : w = 0
  · subst w
    simp [lemma55_actual_zeta_pole_removed_at_one]
  · have hs0 : 1+w ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      have hb := Complex.abs_re_le_norm w
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
      have hlo := (abs_le.mp hb).1
      linarith
    have hs1 : 1+w ≠ 1 := by intro he; apply hw0; linear_combination he
    rw [zetaPoleRemoved_eq_mul_riemannZeta hs0 hs1]
    simp [lemma57RegularizedZeta, hw0]

lemma lemma171_gaussian_factor_hasDerivAt_zero (D : ℕ) :
    HasDerivAt (lemma171GaussianMellinFactor D) (Real.log (lemma56PaperT D) : ℂ) 0 := by
  have haux (a b : ℂ) : HasDerivAt (fun w : ℂ => Complex.exp (a*w+w^2/b)) a 0 := by
    have hh : HasDerivAt (fun w : ℂ => a*w+w^2/b) a 0 := by
      convert ((hasDerivAt_id (0 : ℂ)).const_mul a).add
        (((hasDerivAt_id (0 : ℂ)).pow 2).div_const b) using 1
      simp
    simpa using hh.cexp
  rw [lemma56PaperT, Real.log_exp]
  exact haux _ _

lemma lemma171_residue_prefactor_deriv_exact (D : ℕ) :
    deriv (lemma171ResiduePrefactor D) 0 = deriv (lemma171AnalyticCorrection D) 1 +
      lemma171AnalyticCorrection D 1 *
        (2 * (Real.eulerMascheroniConstant : ℂ) + (Real.log (lemma56PaperT D) : ℂ)) := by
  have hC : HasDerivAt (fun w : ℂ => lemma171AnalyticCorrection D (1+w))
      (deriv (lemma171AnalyticCorrection D) 1) 0 := by
    have hd := (lemma171_correction_analyticOnNhd D 1 (by norm_num)).differentiableAt.hasDerivAt
    have hd' : HasDerivAt (lemma171AnalyticCorrection D)
        (deriv (lemma171AnalyticCorrection D) 1) (1+(0 : ℂ)) := by simpa using hd
    simpa only [Function.comp_def, mul_one] using
      hd'.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add 1)
  have hh := ((hC.mul (lemma171_regular_zeta_hasDerivAt_zero.pow 2)).mul
    (lemma171_gaussian_factor_hasDerivAt_zero D)).deriv
  convert hh using 1
  simp [Pi.mul_apply, Pi.pow_apply, lemma55_actual_zeta_pole_removed_at_one,
    lemma171_gaussian_factor_zero]
  ring

lemma lemma171_correction_one_ne_zero (D : ℕ) : lemma171AnalyticCorrection D 1 ≠ 0 := by
  rw [lemma171_correction_at_one]
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply mul_pos (by positivity)
  apply Finset.prod_pos
  intro p hp
  exact div_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos) (by positivity)

lemma lemma171_log_residue_main_re {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hd : realLDerivAtOne χ ≠ 0) :
    (lemma171LogResidueMain χ).re =
      lemma171MainTerm χ * (Real.log (lemma56PaperT D) +
        (2 * lemma171RealSecondJet χ / realLDerivAtOne χ +
          2 * Real.eulerMascheroniConstant + lemma171CorrectionLogDerivative D)) := by
  have hdC : LDerivAtOne χ ≠ 0 := by
    rw [LDerivAtOne_eq_realLDerivAtOne χ hD]
    exact Complex.ofReal_ne_zero.mpr hd
  have hcC := lemma171_correction_one_ne_zero D
  have hcomplex : lemma171LogResidueMain χ = (lemma171MainTerm χ : ℂ) *
      ((Real.log (lemma56PaperT D) : ℂ) +
        (iteratedDeriv 2 (dirichletLFunction χ) 1 / LDerivAtOne χ +
          2 * (Real.eulerMascheroniConstant : ℂ) +
          deriv (lemma171AnalyticCorrection D) 1 / lemma171AnalyticCorrection D 1)) := by
    rw [lemma171LogResidueMain, lemma171_residue_prefactor_deriv_exact,
      lemma171_main_term_complex χ hD]
    field_simp [hdC, hcC]
    <;> ring
  rw [hcomplex, LDerivAtOne_eq_realLDerivAtOne χ hD]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, Complex.div_ofReal_re, Complex.re_ofNat]
  unfold lemma171RealSecondJet lemma171CorrectionLogDerivative
  ring

end ZhangLS.Spec
