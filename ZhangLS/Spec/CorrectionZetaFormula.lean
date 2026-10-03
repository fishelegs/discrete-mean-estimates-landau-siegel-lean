import ZhangLS.Spec.Lemma171LogDerivative

/-! Exact zeta component of the actual conductor correction logarithmic derivative. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

lemma lemma171_zeta_log_derivative_at_one_eq :
    lemma171ZetaLogDerivativeAtOne = -2 * deriv riemannZeta 2 / riemannZeta 2 := by
  have hz0 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hz : HasDerivAt (fun s : ℂ => riemannZeta (2*s))
      (2 * deriv riemannZeta 2) 1 := by
    have hh := (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).hasDerivAt
    have hh' : HasDerivAt riemannZeta (deriv riemannZeta 2) (2*(1 : ℂ)) := by simpa using hh
    convert hh'.comp 1 ((hasDerivAt_id (1 : ℂ)).const_mul 2) using 1 <;> ring
  have hh := hz.fun_inv (by simpa using hz0)
  unfold lemma171ZetaLogDerivativeAtOne
  rw [logDeriv_apply, hh.deriv]
  norm_num only [mul_one]
  field_simp [hz0]
  <;> ring

lemma lemma171_correction_log_derivative_zeta_formula (D : ℕ) :
    lemma171CorrectionLogDerivative D =
      (-2 * deriv riemannZeta 2 / riemannZeta 2).re +
        ∑ p ∈ D.primeFactors, Real.log (p : ℝ) / ((p : ℝ) + 1) := by
  rw [lemma171_correction_log_derivative_eq, lemma171_zeta_log_derivative_at_one_eq]

end ZhangLS.Spec
