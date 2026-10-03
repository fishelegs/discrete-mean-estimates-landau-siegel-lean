import ZhangLS.Spec.CorrectionZetaFormula

/-! The actual correction quotient is real, so its norm equals the scalar J bound. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Filter Set
open scoped Topology

lemma lemma171_zeta_derivative_two_im_zero : (deriv riemannZeta 2).im = 0 := by
  have hd := (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).hasDerivAt
  have hA : HasFDerivAt ((↑) : ℝ → ℂ) ofRealCLM (2 : ℝ) := ofRealCLM.hasFDerivAt
  have hB : HasFDerivAt riemannZeta
      ((ContinuousLinearMap.smulRight 1 (deriv riemannZeta 2) : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM (2 : ℝ)) := hd.hasFDerivAt.restrictScalars ℝ
  have hC : HasFDerivAt im imCLM (riemannZeta (ofRealCLM (2 : ℝ))) := imCLM.hasFDerivAt
  have him : HasDerivAt (fun x : ℝ => (riemannZeta (x : ℂ)).im)
      (deriv riemannZeta 2).im 2 := by
    simpa using (hC.comp (f := fun x : ℝ => riemannZeta (x : ℂ)) (2 : ℝ)
      (hB.comp (f := ((↑) : ℝ → ℂ)) (2 : ℝ) hA)).hasDerivAt
  have he : (fun x : ℝ => (riemannZeta (x : ℂ)).im) =ᶠ[𝓝 (2 : ℝ)] (fun _ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (2 : ℝ) ∈ Ioi 1)] with x hx
    exact riemannZeta_im_eq_zero_of_one_lt hx
  exact (him.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const 2 (0 : ℝ))

lemma lemma171_correction_log_derivative_complex_formula (D : ℕ) :
    deriv (lemma171AnalyticCorrection D) 1 / lemma171AnalyticCorrection D 1 =
      -2 * deriv riemannZeta 2 / riemannZeta 2 +
        (((∑ p ∈ D.primeFactors, Real.log (p : ℝ) / ((p : ℝ)+1)) : ℝ) : ℂ) := by
  have hz : riemannZeta ((2 : ℂ)*1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hzd : DifferentiableAt ℂ (fun s : ℂ => (riemannZeta (2*s))⁻¹) 1 := by
    have hh : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (2*s)) 1 :=
      (differentiableAt_riemannZeta (by norm_num : (2 : ℂ)*1 ≠ 1)).comp 1
        ((differentiableAt_const (2 : ℂ)).mul differentiableAt_id)
    exact hh.inv hz
  have hr : lemma171RamificationFactor D 1 ≠ 0 := by
    unfold lemma171RamificationFactor
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => inv_ne_zero
      (lemma171_one_add_monomial_ne_zero (Nat.prime_of_mem_primeFactors hp) 1 (by norm_num)))
  have hrd : DifferentiableAt ℂ (lemma171RamificationFactor D) 1 :=
    (lemma171_ramification_differentiableOn D 1 (by norm_num)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))
  change logDeriv (lemma171AnalyticCorrection D) 1 = _
  unfold lemma171AnalyticCorrection
  rw [logDeriv_mul 1 (inv_ne_zero hz) hr hzd hrd,
    lemma171_ramification_log_derivative_at_one, ← lemma171_zeta_log_derivative_at_one_eq]
  rfl

lemma lemma171_correction_log_derivative_is_real (D : ℕ) :
    deriv (lemma171AnalyticCorrection D) 1 / lemma171AnalyticCorrection D 1 =
      (lemma171CorrectionLogDerivative D : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [lemma171_correction_log_derivative_complex_formula]
    have hz : (riemannZeta (2 : ℂ)).im = 0 := by
      simpa using riemannZeta_im_eq_zero_of_one_lt (by norm_num : (1 : ℝ) < 2)
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
    norm_num [Complex.div_im, Complex.mul_im, hz, lemma171_zeta_derivative_two_im_zero]

lemma lemma171_correction_log_derivative_norm_le (D : ℕ) (hD : 3 ≤ D) :
    ‖deriv (lemma171AnalyticCorrection D) 1 / lemma171AnalyticCorrection D 1‖ ≤
      lemma171CorrectionLogDerivativeBound * (1 + Real.log (Real.log (D : ℝ)))^2 := by
  rw [lemma171_correction_log_derivative_is_real, Complex.norm_real, Real.norm_eq_abs]
  exact lemma171_correction_log_derivative_abs_le D hD

end ZhangLS.Spec
