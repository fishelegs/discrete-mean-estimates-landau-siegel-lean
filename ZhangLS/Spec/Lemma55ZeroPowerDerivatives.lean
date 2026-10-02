import ZhangLS.Spec.Lemma55HigherLogDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# Actual zero inverse powers from higher logarithmic derivatives

The local finite sum uses precisely the actual zeros and their actual
analytic orders. Its higher derivatives are identified with inverse
power sums, and the actual analytic remainder bound is transported to
these sums without adding a partial-fraction hypothesis.
-/

namespace ZhangLS.Spec

open Complex Set Finset

lemma lemma55_iterated_deriv_inverse_pole (ρ z : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ => 1 / (w - ρ)) z =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - ρ) ^ (-1 - (n : ℤ)) := by
  have h := iteratedDerivWithin_one_div (𝕜 := ℂ) n isOpen_univ (mem_univ (z - ρ))
  rw [iteratedDerivWithin_univ] at h
  change iteratedDeriv n (fun w => (fun y : ℂ => 1 / y) (w - ρ)) z = _
  rw [iteratedDeriv_comp_sub_const]
  exact h

lemma lemma55_iterated_deriv_weighted_inverse_pole (m ρ z : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ => m / (w - ρ)) z =
      m * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - ρ) ^ (-1 - (n : ℤ))) := by
  have heq : (fun w : ℂ => m / (w - ρ)) = fun w => m * (1 / (w - ρ)) := by
    ext w
    ring
  rw [heq, iteratedDeriv_const_mul_field, lemma55_iterated_deriv_inverse_pole]

noncomputable def lemma55LocalZeroPowerSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) (k : ℕ) : ℂ :=
  ∑ ρ ∈ lemma55LocalZeroFinset χ t,
    (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) /
      (lemma55JensenCenter t - ρ) ^ k

theorem lemma55_actual_local_zero_higher_derivative
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t) =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * lemma55LocalZeroPowerSum χ t (n + 1) := by
  classical
  have hne : ∀ ρ ∈ lemma55LocalZeroFinset χ t, lemma55JensenCenter t - ρ ≠ 0 := by
    intro ρ hρ hzero
    apply lemma55_actual_jensen_center_ne_zero χ t
    rw [sub_eq_zero.mp hzero]
    exact ((lemma55_mem_actual_local_zero_finset χ hD t ρ).mp hρ).2
  have ha : ∀ ρ ∈ lemma55LocalZeroFinset χ t,
      ContDiffAt ℂ n (fun w : ℂ =>
        (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) / (w - ρ))
          (lemma55JensenCenter t) := by
    intro ρ hρ
    exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hne ρ hρ)).contDiffAt
  unfold lemma55LocalZeroLogDerivative lemma55LocalZeroPowerSum
  rw [iteratedDeriv_fun_sum ha, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [lemma55_iterated_deriv_weighted_inverse_pole]
  have he : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, div_eq_mul_inv]
  ring

noncomputable def lemma55NormalizedLogDerivative {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) (n : ℕ) : ℂ :=
  ((-1 : ℂ) ^ n * iteratedDeriv n (logDeriv (dirichletLFunction χ))
      (lemma55JensenCenter t)) / (n.factorial : ℂ)

theorem lemma55_actual_power_sum_remainder_norm_eq
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (n : ℕ) :
    ‖lemma55NormalizedLogDerivative χ t n - lemma55LocalZeroPowerSum χ t (n + 1)‖ =
      ‖iteratedDeriv n (logDeriv (dirichletLFunction χ)) (lemma55JensenCenter t) -
        iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t)‖ /
          (n.factorial : ℝ) := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hid : lemma55NormalizedLogDerivative χ t n - lemma55LocalZeroPowerSum χ t (n + 1) =
      ((-1 : ℂ) ^ n / (n.factorial : ℂ)) *
        (iteratedDeriv n (logDeriv (dirichletLFunction χ)) (lemma55JensenCenter t) -
          iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t)) := by
    rw [lemma55_actual_local_zero_higher_derivative χ hD t n]
    unfold lemma55NormalizedLogDerivative
    field_simp
    linear_combination (lemma55LocalZeroPowerSum χ t (n + 1) * (n.factorial : ℂ)) * he
  rw [hid, norm_mul, norm_div, norm_pow]
  simp only [norm_neg, norm_one, one_pow, norm_natCast]
  ring

theorem lemma55_actual_power_sum_remainder_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖lemma55NormalizedLogDerivative χ t n - lemma55LocalZeroPowerSum χ t (n + 1)‖ ≤
      990 * ((n : ℝ) + 1) * Real.log (D : ℝ) * (8 / 9 : ℝ) ^ (n + 1) := by
  rw [lemma55_actual_power_sum_remainder_norm_eq χ hD t n]
  exact lemma55_actual_normalized_logDeriv_remainder_bound χ hD hL ht n

theorem lemma55_actual_power_sum_remainder_sum_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (S : Finset ℕ) :
    (∑ n ∈ S,
      ‖lemma55NormalizedLogDerivative χ t n - lemma55LocalZeroPowerSum χ t (n + 1)‖) ≤
        71280 * Real.log (D : ℝ) := by
  simp_rw [lemma55_actual_power_sum_remainder_norm_eq χ hD t]
  exact lemma55_actual_logDeriv_remainder_sum_bound χ hD hL ht S

end ZhangLS.Spec
