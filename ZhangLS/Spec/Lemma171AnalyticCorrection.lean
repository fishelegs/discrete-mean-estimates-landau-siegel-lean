import ZhangLS.Spec.Lemma171DirichletSeries
import ZhangLS.Spec.RealAxisDerivativeAtOne
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Lemma 17.1: holomorphic correction and exact main-term normalization

The correction is proved holomorphic in Re s>1/2, so its value at s=1 is a genuine
analytic value. It yields exactly a after multiplication by the actual L′(1,χ)².
Uniform bounds for the remaining residue terms are proved in `Lemma171ResidueBound.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma171_ramification_differentiableOn (D : ℕ) :
    DifferentiableOn ℂ (lemma171RamificationFactor D) {s : ℂ | 0 < s.re} := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  unfold lemma171RamificationFactor
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  apply DifferentiableAt.inv
  · exact (differentiableAt_const (1 : ℂ)).add (lemma32_prime_monomial_differentiable p s)
  · exact lemma171_one_add_monomial_ne_zero (Nat.prime_of_mem_primeFactors hp) s hs

/-- The correction really is holomorphic throughout Re s > 1/2, including s=1. -/
lemma lemma171_correction_analyticOnNhd (D : ℕ) :
    AnalyticOnNhd ℂ (lemma171AnalyticCorrection D) {s : ℂ | 1/2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change 1/2 < s.re at hs
  have h2 : 1 < (2*s).re := by simp only [Complex.mul_re]; norm_num; linarith [hs]
  have hne : 2*s ≠ 1 := by intro h; rw [h] at h2; norm_num at h2
  have hz : DifferentiableAt ℂ (fun u : ℂ => riemannZeta (2*u)) s :=
    (differentiableAt_riemannZeta hne).comp s ((differentiableAt_const (2 : ℂ)).mul differentiableAt_id)
  have hr := lemma171_ramification_differentiableOn D s (by change 0 < s.re; linarith [hs])
  exact (hz.inv (riemannZeta_ne_zero_of_one_lt_re h2)).differentiableWithinAt.mul (hr.mono (by intro z hz; change 1/2 < z.re at hz; change 0 < z.re; linarith))

lemma lemma171_prime_monomial_one {p : ℕ} (hp : 0 < p) :
    lemma32PrimeMonomial p 1 = (p : ℂ)⁻¹ := by
  rw [lemma32_prime_monomial_eq_cpow hp]
  rw [Complex.cpow_neg,Complex.cpow_one]

lemma lemma171_ramification_at_one (D : ℕ) :
    lemma171RamificationFactor D 1 =
      ((∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1) : ℝ) : ℂ) := by
  unfold lemma171RamificationFactor
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  rw [lemma171_prime_monomial_one hpr.pos]
  have hn : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have ha : (p : ℂ)+1 ≠ 0 := by
    have hr : 0 < (p : ℝ)+1 := by positivity
    exact_mod_cast hr.ne'
  field_simp

lemma lemma171_correction_at_one (D : ℕ) :
    lemma171AnalyticCorrection D 1 =
      (((6 / Real.pi^2) * ∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1) : ℝ) : ℂ) := by
  simp only [lemma171AnalyticCorrection,mul_one,riemannZeta_two,lemma171_ramification_at_one,
    inv_div]
  push_cast
  rfl

/-- The leading L′² contribution to the true residue has precisely the paper's constant. -/
lemma lemma171_main_term_complex {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (lemma171MainTerm χ : ℂ) = lemma171AnalyticCorrection D 1 * LDerivAtOne χ^2 := by
  rw [lemma171_correction_at_one,LDerivAtOne_eq_realLDerivAtOne χ hD]
  unfold lemma171MainTerm
  push_cast
  ring



end ZhangLS.Spec
