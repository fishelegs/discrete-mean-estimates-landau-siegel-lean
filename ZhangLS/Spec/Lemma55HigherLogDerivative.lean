import ZhangLS.Spec.Lemma55LocalLogDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Actual all-order logarithmic-derivative remainders

At every center 2+it, the iterated actual logarithmic derivative differs
from that of the actual finite zero sum by the derivative of the actual
zero-removed analytic factor. After division by n!, the remainder is
bounded by 990(n+1)log D (8/9)^(n+1).
-/

namespace ZhangLS.Spec

open Complex Metric Set Filter
open scoped Topology Real

noncomputable def lemma55LocalZeroLogDerivative {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ lemma55LocalZeroFinset χ t,
    (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) / (z - ρ)

theorem lemma55_actual_zero_removed_higher_logDeriv_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (lemma55ZeroRemovedL χ t)) (lemma55JensenCenter t)‖ ≤
      (n + 1).factorial * (990 * Real.log (D : ℝ)) / (9 / 8 : ℝ) ^ (n + 1) := by
  obtain ⟨ℓ, hℓ⟩ := lemma55_actual_zero_removed_log_exists χ hD t
  have heq : deriv ℓ =ᶠ[𝓝 (0 : ℂ)] fun z =>
      logDeriv (lemma55ZeroRemovedL χ t) (lemma55JensenCenter t + z) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball (0 : ℂ) (5 / 4 : ℝ))] with z hz
    exact (lemma55_actual_zero_removed_log_hasDerivAt χ hD hℓ hz).deriv
  have hj : iteratedDeriv n (deriv ℓ) 0 =
      iteratedDeriv n (logDeriv (lemma55ZeroRemovedL χ t)) (lemma55JensenCenter t) := by
    simpa only [iteratedDeriv_comp_const_add, add_zero] using heq.iteratedDeriv_eq n
  rw [← hj, ← iteratedDeriv_succ']
  exact lemma55_actual_zero_removed_log_cauchy_bound χ hD hL ht hℓ (n + 1)

theorem lemma55_actual_higher_logDeriv_remainder_eq
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logDeriv (dirichletLFunction χ)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t) =
        iteratedDeriv n (logDeriv (lemma55ZeroRemovedL χ t)) (lemma55JensenCenter t) := by
  let c := lemma55JensenCenter t
  have hf := lemma55_actual_jensen_center_ne_zero χ t
  have hP : lemma55LocalZeroFactor χ t c ≠ 0 := by
    intro hz
    apply hf
    rw [lemma55_actual_zero_factorization χ hD t c, hz, zero_mul]
  have haF : AnalyticAt ℂ (logDeriv (dirichletLFunction χ)) c :=
    (lemma55_actual_L_analyticOnNhd χ hD c (mem_univ c)).deriv.div
      (lemma55_actual_L_analyticOnNhd χ hD c (mem_univ c)) hf
  have haP : AnalyticAt ℂ (logDeriv (lemma55LocalZeroFactor χ t)) c :=
    (lemma55_actual_zero_factor_analytic χ hD t c (mem_univ c)).deriv.div
      (lemma55_actual_zero_factor_analytic χ hD t c (mem_univ c)) hP
  have hfn : ∀ᶠ z in 𝓝 c, dirichletLFunction χ z ≠ 0 :=
    (lemma55_actual_L_analyticOnNhd χ hD c (mem_univ c)).continuousAt.eventually_ne hf
  have hPn : ∀ᶠ z in 𝓝 c, lemma55LocalZeroFactor χ t z ≠ 0 :=
    (lemma55_actual_zero_factor_analytic χ hD t c (mem_univ c)).continuousAt.eventually_ne hP
  have hsum : logDeriv (lemma55LocalZeroFactor χ t) =ᶠ[𝓝 c]
      lemma55LocalZeroLogDerivative χ t := by
    filter_upwards [hPn] with z hz
    exact lemma55_actual_zero_factor_logDeriv χ hD hz
  have heq : (logDeriv (dirichletLFunction χ) - logDeriv (lemma55LocalZeroFactor χ t))
      =ᶠ[𝓝 c] logDeriv (lemma55ZeroRemovedL χ t) := by
    filter_upwards [hfn, hPn] with z hz hp
    change logDeriv (dirichletLFunction χ) z - logDeriv (lemma55LocalZeroFactor χ t) z = _
    rw [lemma55_actual_local_logDeriv_formula χ hD t hz,
      lemma55_actual_zero_factor_logDeriv χ hD hp, add_sub_cancel_left]
  have hj := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_sub haF.contDiffAt haP.contDiffAt, hsum.iteratedDeriv_eq n] at hj
  exact hj

theorem lemma55_actual_higher_logDeriv_remainder_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (dirichletLFunction χ)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t)‖ ≤
        (n + 1).factorial * (990 * Real.log (D : ℝ)) / (9 / 8 : ℝ) ^ (n + 1) := by
  rw [lemma55_actual_higher_logDeriv_remainder_eq χ hD t n]
  exact lemma55_actual_zero_removed_higher_logDeriv_bound χ hD hL ht n

theorem lemma55_actual_normalized_logDeriv_remainder_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (dirichletLFunction χ)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t)‖ /
        (n.factorial : ℝ) ≤
          990 * ((n : ℝ) + 1) * Real.log (D : ℝ) * (8 / 9 : ℝ) ^ (n + 1) := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
  calc
    _ ≤ (n + 1).factorial * (990 * Real.log (D : ℝ)) / (9 / 8 : ℝ) ^ (n + 1) :=
      lemma55_actual_higher_logDeriv_remainder_bound χ hD hL ht n
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        div_eq_mul_inv, ← inv_pow, inv_div]
      ring

theorem lemma55_actual_logDeriv_remainder_sum_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (S : Finset ℕ) :
    (∑ n ∈ S,
      ‖iteratedDeriv n (logDeriv (dirichletLFunction χ)) (lemma55JensenCenter t) -
        iteratedDeriv n (lemma55LocalZeroLogDerivative χ t) (lemma55JensenCenter t)‖ /
          (n.factorial : ℝ)) ≤ 71280 * Real.log (D : ℝ) := by
  have hr : ‖(8 / 9 : ℝ)‖ < 1 := by norm_num
  have hs : HasSum (fun n : ℕ => ((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n) (81 : ℝ) := by
    convert (hasSum_coe_mul_geometric_of_norm_lt_one hr).add (hasSum_geometric_of_norm_lt_one hr) using 1
    · ext n
      ring
    · norm_num
  have hsum : (∑ n ∈ S, ((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n) ≤ 81 := by
    calc
      _ ≤ ∑' n : ℕ, ((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n :=
        hs.summable.sum_le_tsum S (fun n _ => by positivity)
      _ = 81 := hs.tsum_eq
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  calc
    _ ≤ ∑ n ∈ S, (880 * Real.log (D : ℝ)) * (((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n) := by
      apply Finset.sum_le_sum
      intro n _
      have hb := lemma55_actual_normalized_logDeriv_remainder_bound χ hD hL ht n
      apply hb.trans_eq
      rw [pow_succ]
      ring
    _ = (880 * Real.log (D : ℝ)) * ∑ n ∈ S, ((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n := by
      rw [Finset.mul_sum]
    _ ≤ (880 * Real.log (D : ℝ)) * 81 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 71280 * Real.log (D : ℝ) := by ring

end ZhangLS.Spec
