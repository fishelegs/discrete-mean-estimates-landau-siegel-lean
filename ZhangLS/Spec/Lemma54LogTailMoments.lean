import ZhangLS.Spec.Lemma54MellinSecondMoment

/-! # Exact positive-axis log-Gaussian moments and a uniform cubic envelope -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma54_log_tail_after_exp (B q u : ℝ) :
    Real.exp u * ((Real.exp u) ^ q * Real.exp (-((B * Real.log (Real.exp u) / 100) ^ 2))) =
      Real.exp ((q + 1) * u - (B / 100) ^ 2 * u ^ 2) := by
  rw [Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem lemma54_log_tail_moment_integrable {B : ℝ} (hB : 0 < B) (q : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-((B * Real.log x / 100) ^ 2))) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u (_ : u ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun x : ℝ => x ^ q * Real.exp (-((B * Real.log x / 100) ^ 2)))
  simp only [image_univ, Real.range_exp, integrableOn_univ,
    abs_of_pos (Real.exp_pos _), smul_eq_mul, lemma54_log_tail_after_exp] at h
  exact h.mpr (lemma54_real_gaussian_integrable (by positivity : 0 < B / 100) (q + 1))

theorem lemma54_log_tail_moment_integral {B : ℝ} (hB : 0 < B) (q : ℝ) :
    (∫ x : ℝ in Ioi 0, x ^ q * Real.exp (-((B * Real.log x / 100) ^ 2))) =
      Real.sqrt Real.pi / (B / 100) * Real.exp ((q + 1) ^ 2 / (4 * (B / 100) ^ 2)) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u (_ : u ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun x : ℝ => x ^ q * Real.exp (-((B * Real.log x / 100) ^ 2)))
  simp only [image_univ, Real.range_exp, setIntegral_univ,
    abs_of_pos (Real.exp_pos _), smul_eq_mul, lemma54_log_tail_after_exp] at h
  exact h.trans (lemma54_real_gaussian_integral (by positivity : 0 < B / 100) (q + 1))

theorem lemma54_log_cubic_tail_integrable {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun x : ℝ => (1 + x ^ 3) * Real.exp (-((B * Real.log x / 100) ^ 2)))
      (Ioi 0) := by
  have h0 := lemma54_log_tail_moment_integrable hB 0
  have h3 := lemma54_log_tail_moment_integrable hB 3
  simp only [Real.rpow_zero, one_mul] at h0
  simp only [Real.rpow_ofNat] at h3
  have hh : IntegrableOn (fun x : ℝ =>
      Real.exp (-((B * Real.log x / 100) ^ 2)) +
        x ^ 3 * Real.exp (-((B * Real.log x / 100) ^ 2))) (Ioi 0) := h0.add h3
  simpa only [add_mul, one_mul] using hh

theorem lemma54_log_cubic_tail_integral_bound {B : ℝ} (hB : 200 ≤ B) :
    (∫ x : ℝ in Ioi 0, (1 + x ^ 3) * Real.exp (-((B * Real.log x / 100) ^ 2))) ≤
      200 * Real.sqrt Real.pi * Real.exp 1 := by
  have hB0 : 0 < B := by linarith
  have h0 := lemma54_log_tail_moment_integrable hB0 0
  have h3 := lemma54_log_tail_moment_integrable hB0 3
  have h0eq := lemma54_log_tail_moment_integral hB0 0
  have h3eq := lemma54_log_tail_moment_integral hB0 3
  simp only [Real.rpow_zero, one_mul] at h0 h0eq
  simp only [Real.rpow_ofNat] at h3 h3eq
  simp_rw [add_mul, one_mul]
  rw [integral_add h0 h3, h0eq, h3eq]
  have hs : 4 ≤ (B / 100) ^ 2 := by
    have hb : 2 ≤ B / 100 := by linarith
    nlinarith
  have he1 : Real.exp ((0 + 1 : ℝ) ^ 2 / (4 * (B / 100) ^ 2)) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_one (by positivity : 0 < 4 * (B / 100) ^ 2)).mpr
    nlinarith
  have he4 : Real.exp ((3 + 1 : ℝ) ^ 2 / (4 * (B / 100) ^ 2)) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_one (by positivity : 0 < 4 * (B / 100) ^ 2)).mpr
    nlinarith
  have hp : Real.sqrt Real.pi / (B / 100) ≤ 100 * Real.sqrt Real.pi := by
    apply (div_le_iff₀ (by positivity : 0 < B / 100)).mpr
    have hB1 : 1 ≤ B := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hB1 (Real.sqrt_nonneg Real.pi)]
  have hh1 := mul_le_mul hp he1 (Real.exp_nonneg _) (by positivity : 0 ≤ 100 * Real.sqrt Real.pi)
  have hh4 := mul_le_mul hp he4 (Real.exp_nonneg _) (by positivity : 0 ≤ 100 * Real.sqrt Real.pi)
  nlinarith only [hh1, hh4]

end ZhangLS.Spec
