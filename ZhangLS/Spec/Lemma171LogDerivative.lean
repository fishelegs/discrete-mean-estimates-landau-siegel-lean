import ZhangLS.Spec.Lemma171AnalyticCorrection
import ZhangLS.Spec.Lemma83FinitePrimeBounds
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Actual logarithmic derivative of the Lemma 17.1 correction

The finite ramification product contributes exactly `∑_{p | D} log p / (p+1)`.
The remaining logarithmic derivative is a fixed zeta value, independent of the
conductor. The existing elementary prime-divisor estimate then gives the
required squared-log-log bound for the actual analytic correction.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical

/-- The zeta contribution is an actual analytic derivative, independent of D. -/
noncomputable def lemma171ZetaLogDerivativeAtOne : ℂ :=
  logDeriv (fun s : ℂ => (riemannZeta (2*s))⁻¹) 1

/-- The real logarithmic derivative of the actual correction. -/
noncomputable def lemma171CorrectionLogDerivative (D : ℕ) : ℝ :=
  (deriv (lemma171AnalyticCorrection D) 1 / lemma171AnalyticCorrection D 1).re

noncomputable def lemma171CorrectionLogDerivativeBound : ℝ :=
  |lemma171ZetaLogDerivativeAtOne.re| + 1

lemma lemma171_correction_log_derivative_bound_pos :
    0 < lemma171CorrectionLogDerivativeBound := by
  unfold lemma171CorrectionLogDerivativeBound
  positivity

lemma lemma171_prime_monomial_hasDerivAt (p : ℕ) (s : ℂ) :
    HasDerivAt (lemma32PrimeMonomial p)
      (lemma32PrimeMonomial p s * (-(Real.log (p : ℝ) : ℂ))) s := by
  simpa only [lemma32PrimeMonomial, neg_one_mul] using
    (((hasDerivAt_id s).neg).mul_const (Real.log (p : ℝ) : ℂ)).cexp

lemma lemma171_ramified_log_derivative_at_one {p : ℕ} (hp : p.Prime) :
    logDeriv (fun s : ℂ => (1+lemma32PrimeMonomial p s)⁻¹) 1 =
      ((Real.log (p : ℝ) / ((p : ℝ)+1) : ℝ) : ℂ) := by
  have hn := lemma171_one_add_monomial_ne_zero hp 1 (by norm_num)
  have hd := ((lemma171_prime_monomial_hasDerivAt p 1).const_add 1).fun_inv hn
  rw [logDeriv_apply, hd.deriv, lemma171_prime_monomial_one hp.pos]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p : ℂ)+1 ≠ 0 := by
    have hh : (0 : ℝ) < (p : ℝ)+1 := by positivity
    exact_mod_cast hh.ne'
  have hp1' : (1 : ℂ)+(p : ℂ) ≠ 0 := by simpa only [add_comm] using hp1
  have hone : (1 : ℂ)+(p : ℂ)⁻¹ ≠ 0 := by
    simpa only [lemma171_prime_monomial_one hp.pos] using hn
  push_cast
  field_simp [hp0, hp1, hp1', hone]
  all_goals ring

lemma lemma171_ramification_log_derivative_at_one (D : ℕ) :
    logDeriv (lemma171RamificationFactor D) 1 =
      (((∑ p ∈ D.primeFactors, Real.log (p : ℝ)/((p : ℝ)+1)) : ℝ) : ℂ) := by
  have hne (p : ℕ) (hp : p ∈ D.primeFactors) :
      (1+lemma32PrimeMonomial p 1)⁻¹ ≠ 0 :=
    inv_ne_zero (lemma171_one_add_monomial_ne_zero
      (Nat.prime_of_mem_primeFactors hp) 1 (by norm_num))
  have hd (p : ℕ) (hp : p ∈ D.primeFactors) :
      DifferentiableAt ℂ (fun s : ℂ => (1+lemma32PrimeMonomial p s)⁻¹) 1 := by
    exact ((differentiableAt_const (1 : ℂ)).add
      (lemma32_prime_monomial_differentiable p 1)).inv
      (lemma171_one_add_monomial_ne_zero (Nat.prime_of_mem_primeFactors hp) 1 (by norm_num))
  unfold lemma171RamificationFactor
  rw [logDeriv_prod hne hd]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact lemma171_ramified_log_derivative_at_one (Nat.prime_of_mem_primeFactors hp)

/-- Exact evaluation of the actual logarithmic derivative; no replacement
correction or freely chosen error term appears. -/
lemma lemma171_correction_log_derivative_eq (D : ℕ) :
    lemma171CorrectionLogDerivative D = lemma171ZetaLogDerivativeAtOne.re +
      ∑ p ∈ D.primeFactors, Real.log (p : ℝ)/((p : ℝ)+1) := by
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
  have hrd : DifferentiableAt ℂ (lemma171RamificationFactor D) 1 := by
    exact (lemma171_ramification_differentiableOn D 1 (by norm_num)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))
  change (logDeriv (lemma171AnalyticCorrection D) 1).re = _
  unfold lemma171AnalyticCorrection
  rw [logDeriv_mul 1 (inv_ne_zero hz) hr hzd hrd,
    lemma171_ramification_log_derivative_at_one, Complex.add_re, Complex.ofReal_re]
  rfl

lemma lemma171_ramified_log_derivative_sum_nonneg (D : ℕ) :
    0 ≤ ∑ p ∈ D.primeFactors, Real.log (p : ℝ)/((p : ℝ)+1) := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr
    (Nat.prime_of_mem_primeFactors hp).one_lt.le)) (by positivity)

lemma lemma171_ramified_log_derivative_sum_le (D : ℕ) :
    (∑ p ∈ D.primeFactors, Real.log (p : ℝ)/((p : ℝ)+1)) ≤
      ∑ p ∈ D.primeFactors, Real.log (p : ℝ)/(p : ℝ) := by
  apply Finset.sum_le_sum
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  exact div_le_div_of_nonneg_left
    (Real.log_nonneg (Nat.one_le_cast.mpr hpr.one_lt.le))
    (Nat.cast_pos.mpr hpr.pos) (by linarith)

/-- An explicit absolute constant bounds the actual logarithmic derivative for
all conductors at least three. -/
lemma lemma171_correction_log_derivative_abs_le (D : ℕ) (hD : 3 ≤ D) :
    |lemma171CorrectionLogDerivative D| ≤
      lemma171CorrectionLogDerivativeBound * (1+Real.log (Real.log (D : ℝ)))^2 := by
  have hlog := lemma83_log_nat_gt_one hD
  have hll := Real.log_nonneg hlog.le
  have hb : 1 ≤ (1+Real.log (Real.log (D : ℝ)))^2 := by nlinarith
  have hsum := (lemma171_ramified_log_derivative_sum_le D).trans
    (lemma83_prime_log_sum_le_loglog D (by omega) hlog)
  rw [lemma171_correction_log_derivative_eq]
  calc
    _ ≤ |lemma171ZetaLogDerivativeAtOne.re| +
        |∑ p ∈ D.primeFactors, Real.log (p : ℝ)/((p : ℝ)+1)| := abs_add_le _ _
    _ = |lemma171ZetaLogDerivativeAtOne.re| +
        ∑ p ∈ D.primeFactors, Real.log (p : ℝ)/((p : ℝ)+1) := by
          rw [abs_of_nonneg (lemma171_ramified_log_derivative_sum_nonneg D)]
    _ ≤ |lemma171ZetaLogDerivativeAtOne.re| + (1+Real.log (Real.log (D : ℝ)))^2 :=
      add_le_add_right hsum _
    _ ≤ _ := by
      unfold lemma171CorrectionLogDerivativeBound
      have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg lemma171ZetaLogDerivativeAtOne.re)
      nlinarith

/-- The source-defined correction logarithmic derivative has the required
uniform squared-log-log bound, with no character-dependent constant. -/
lemma lemma171_correction_log_derivative_eventually :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ D : ℕ in atTop,
      |(deriv (lemma171AnalyticCorrection D) 1 / lemma171AnalyticCorrection D 1).re| ≤
        C * (1+Real.log (Real.log (D : ℝ)))^2 := by
  refine ⟨lemma171CorrectionLogDerivativeBound,
    lemma171_correction_log_derivative_bound_pos, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with D hD
  exact lemma171_correction_log_derivative_abs_le D hD

end ZhangLS.Spec
