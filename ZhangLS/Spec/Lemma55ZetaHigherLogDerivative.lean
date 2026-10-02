import ZhangLS.Spec.Lemma55ZetaLocalLogDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Actual all-order logarithmic-derivative remainders

At every center 2+it, the iterated actual pole-removed zeta logarithmic derivative differs
from that of the actual finite zero sum by the derivative of the actual
zero-removed analytic factor. After division by n!, the remainder is
bounded by 1350(n+1)log D (8/9)^(n+1).
-/

namespace ZhangLS.Spec

open Complex Metric Set Filter
open scoped Topology Real

noncomputable def lemma55ZetaLocalZeroLogDerivative (t : ℝ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
    (analyticOrderNatAt (zetaPoleRemoved) ρ : ℂ) / (z - ρ)

theorem lemma55_actual_zeta_zero_removed_higher_logDeriv_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (lemma55ZetaZeroRemoved t)) (lemma55JensenCenter t)‖ ≤
      (n + 1).factorial * (1350 * Real.log (D : ℝ)) / (9 / 8 : ℝ) ^ (n + 1) := by
  obtain ⟨ℓ, hℓ⟩ := lemma55_actual_zeta_zero_removed_log_exists t
  have heq : deriv ℓ =ᶠ[𝓝 (0 : ℂ)] fun z =>
      logDeriv (lemma55ZetaZeroRemoved t) (lemma55JensenCenter t + z) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball (0 : ℂ) (5 / 4 : ℝ))] with z hz
    exact (lemma55_actual_zeta_zero_removed_log_hasDerivAt hℓ hz).deriv
  have hj : iteratedDeriv n (deriv ℓ) 0 =
      iteratedDeriv n (logDeriv (lemma55ZetaZeroRemoved t)) (lemma55JensenCenter t) := by
    simpa only [iteratedDeriv_comp_const_add, add_zero] using heq.iteratedDeriv_eq n
  rw [← hj, ← iteratedDeriv_succ']
  exact lemma55_actual_zeta_zero_removed_log_cauchy_bound hD hL ht hℓ (n + 1)

theorem lemma55_actual_zeta_higher_logDeriv_remainder_eq
    (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logDeriv (zetaPoleRemoved)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma55ZetaLocalZeroLogDerivative t) (lemma55JensenCenter t) =
        iteratedDeriv n (logDeriv (lemma55ZetaZeroRemoved t)) (lemma55JensenCenter t) := by
  let c := lemma55JensenCenter t
  have hf := (norm_pos_iff.mp (by
    have hb := lemma55_actual_zeta_pole_removed_center_lower t
    linarith only [hb]) : zetaPoleRemoved c ≠ 0)
  have hP : lemma55ZetaLocalZeroFactor t c ≠ 0 := by
    intro hz
    apply hf
    rw [lemma55_actual_zeta_zero_factorization t (by simp [c] : 0 < c.re), hz, zero_mul]
  have haF : AnalyticAt ℂ (logDeriv (zetaPoleRemoved)) c :=
    (lemma55_actual_zeta_pole_removed_analyticAt (by simp [c] : 0 < c.re)).deriv.div
      (lemma55_actual_zeta_pole_removed_analyticAt (by simp [c] : 0 < c.re)) hf
  have haP : AnalyticAt ℂ (logDeriv (lemma55ZetaLocalZeroFactor t)) c :=
    (lemma55_actual_zeta_zero_factor_analytic t c (mem_univ c)).deriv.div
      (lemma55_actual_zeta_zero_factor_analytic t c (mem_univ c)) hP
  have hfn : ∀ᶠ z in 𝓝 c, zetaPoleRemoved z ≠ 0 :=
    (lemma55_actual_zeta_pole_removed_analyticAt (by simp [c] : 0 < c.re)).continuousAt.eventually_ne hf
  have hPn : ∀ᶠ z in 𝓝 c, lemma55ZetaLocalZeroFactor t z ≠ 0 :=
    (lemma55_actual_zeta_zero_factor_analytic t c (mem_univ c)).continuousAt.eventually_ne hP
  have hsum : logDeriv (lemma55ZetaLocalZeroFactor t) =ᶠ[𝓝 c]
      lemma55ZetaLocalZeroLogDerivative t := by
    filter_upwards [hPn] with z hz
    exact lemma55_actual_zeta_zero_factor_logDeriv hz
  have heq : (logDeriv (zetaPoleRemoved) - logDeriv (lemma55ZetaLocalZeroFactor t))
      =ᶠ[𝓝 c] logDeriv (lemma55ZetaZeroRemoved t) := by
    filter_upwards [hfn, hPn,
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp [c] : 0 < c.re)] with z hz hp hzre
    change logDeriv (zetaPoleRemoved) z - logDeriv (lemma55ZetaLocalZeroFactor t) z = _
    rw [lemma55_actual_zeta_removed_local_logDeriv_formula t hzre hz,
      lemma55_actual_zeta_zero_factor_logDeriv hp, add_sub_cancel_left]
  have hj := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_sub haF.contDiffAt haP.contDiffAt, hsum.iteratedDeriv_eq n] at hj
  exact hj

theorem lemma55_actual_zeta_higher_logDeriv_remainder_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (zetaPoleRemoved)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma55ZetaLocalZeroLogDerivative t) (lemma55JensenCenter t)‖ ≤
        (n + 1).factorial * (1350 * Real.log (D : ℝ)) / (9 / 8 : ℝ) ^ (n + 1) := by
  rw [lemma55_actual_zeta_higher_logDeriv_remainder_eq t n]
  exact lemma55_actual_zeta_zero_removed_higher_logDeriv_bound hD hL ht n

theorem lemma55_actual_zeta_normalized_logDeriv_remainder_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (zetaPoleRemoved)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma55ZetaLocalZeroLogDerivative t) (lemma55JensenCenter t)‖ /
        (n.factorial : ℝ) ≤
          1350 * ((n : ℝ) + 1) * Real.log (D : ℝ) * (8 / 9 : ℝ) ^ (n + 1) := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
  calc
    _ ≤ (n + 1).factorial * (1350 * Real.log (D : ℝ)) / (9 / 8 : ℝ) ^ (n + 1) :=
      lemma55_actual_zeta_higher_logDeriv_remainder_bound hD hL ht n
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        div_eq_mul_inv, ← inv_pow, inv_div]
      ring

theorem lemma55_actual_zeta_logDeriv_remainder_sum_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (S : Finset ℕ) :
    (∑ n ∈ S,
      ‖iteratedDeriv n (logDeriv (zetaPoleRemoved)) (lemma55JensenCenter t) -
        iteratedDeriv n (lemma55ZetaLocalZeroLogDerivative t) (lemma55JensenCenter t)‖ /
          (n.factorial : ℝ)) ≤ 97200 * Real.log (D : ℝ) := by
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
    _ ≤ ∑ n ∈ S, (1200 * Real.log (D : ℝ)) * (((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n) := by
      apply Finset.sum_le_sum
      intro n _
      have hb := lemma55_actual_zeta_normalized_logDeriv_remainder_bound hD hL ht n
      apply hb.trans_eq
      rw [pow_succ]
      ring
    _ = (1200 * Real.log (D : ℝ)) * ∑ n ∈ S, ((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n := by
      rw [Finset.mul_sum]
    _ ≤ (1200 * Real.log (D : ℝ)) * 81 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 97200 * Real.log (D : ℝ) := by ring

end ZhangLS.Spec
