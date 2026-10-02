import ZhangLS.Spec.Lemma56LocalLogDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed

/-! # All-order actual logarithmic derivative remainders

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

noncomputable def lemma56LocalZeroLogDerivative {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ lemma56LocalZeroFinset θ t,
    (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) / (z - ρ)

theorem lemma56_actual_zero_removed_higher_logDeriv_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (lemma56ZeroRemovedL θ t)) (lemma55JensenCenter t)‖ ≤
      (n + 1).factorial * (450 * lemma56JensenLogSize θ t) / (9 / 8 : ℝ) ^ (n + 1) := by
  obtain ⟨ℓ, hℓ⟩ := lemma56_actual_zero_removed_log_exists θ hθ t
  have heq : deriv ℓ =ᶠ[𝓝 (0 : ℂ)] fun z =>
      logDeriv (lemma56ZeroRemovedL θ t) (lemma55JensenCenter t + z) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball (0 : ℂ) (5 / 4 : ℝ))] with z hz
    exact (lemma56_actual_zero_removed_log_hasDerivAt θ hθ hℓ hz).deriv
  have hj : iteratedDeriv n (deriv ℓ) 0 =
      iteratedDeriv n (logDeriv (lemma56ZeroRemovedL θ t)) (lemma55JensenCenter t) := by
    simpa only [iteratedDeriv_comp_const_add, add_zero] using heq.iteratedDeriv_eq n
  rw [← hj, ← iteratedDeriv_succ']
  exact lemma56_actual_zero_removed_log_cauchy_bound θ hθ hℓ (n + 1)

theorem lemma56_actual_higher_logDeriv_remainder_eq
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logDeriv (DirichletCharacter.LFunction θ)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma56LocalZeroLogDerivative θ t) (lemma55JensenCenter t) =
        iteratedDeriv n (logDeriv (lemma56ZeroRemovedL θ t)) (lemma55JensenCenter t) := by
  let c := lemma55JensenCenter t
  have hf := lemma56_actual_jensen_center_ne_zero θ t
  have hP : lemma56LocalZeroFactor θ t c ≠ 0 := by
    intro hz
    apply hf
    rw [lemma56_actual_zero_factorization θ hθ t c, hz, zero_mul]
  have haF : AnalyticAt ℂ (logDeriv (DirichletCharacter.LFunction θ)) c :=
    (lemma56_actual_L_analyticOnNhd θ hθ c (mem_univ c)).deriv.div
      (lemma56_actual_L_analyticOnNhd θ hθ c (mem_univ c)) hf
  have haP : AnalyticAt ℂ (logDeriv (lemma56LocalZeroFactor θ t)) c :=
    (lemma56_actual_zero_factor_analytic θ hθ t c (mem_univ c)).deriv.div
      (lemma56_actual_zero_factor_analytic θ hθ t c (mem_univ c)) hP
  have hfn : ∀ᶠ z in 𝓝 c, DirichletCharacter.LFunction θ z ≠ 0 :=
    (lemma56_actual_L_analyticOnNhd θ hθ c (mem_univ c)).continuousAt.eventually_ne hf
  have hPn : ∀ᶠ z in 𝓝 c, lemma56LocalZeroFactor θ t z ≠ 0 :=
    (lemma56_actual_zero_factor_analytic θ hθ t c (mem_univ c)).continuousAt.eventually_ne hP
  have hsum : logDeriv (lemma56LocalZeroFactor θ t) =ᶠ[𝓝 c]
      lemma56LocalZeroLogDerivative θ t := by
    filter_upwards [hPn] with z hz
    exact lemma56_actual_zero_factor_logDeriv θ hθ hz
  have heq : (logDeriv (DirichletCharacter.LFunction θ) - logDeriv (lemma56LocalZeroFactor θ t))
      =ᶠ[𝓝 c] logDeriv (lemma56ZeroRemovedL θ t) := by
    filter_upwards [hfn, hPn] with z hz hp
    change logDeriv (DirichletCharacter.LFunction θ) z - logDeriv (lemma56LocalZeroFactor θ t) z = _
    rw [lemma56_actual_local_logDeriv_formula θ hθ t hz,
      lemma56_actual_zero_factor_logDeriv θ hθ hp, add_sub_cancel_left]
  have hj := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_sub haF.contDiffAt haP.contDiffAt, hsum.iteratedDeriv_eq n] at hj
  exact hj

theorem lemma56_actual_higher_logDeriv_remainder_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction θ)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma56LocalZeroLogDerivative θ t) (lemma55JensenCenter t)‖ ≤
        (n + 1).factorial * (450 * lemma56JensenLogSize θ t) / (9 / 8 : ℝ) ^ (n + 1) := by
  rw [lemma56_actual_higher_logDeriv_remainder_eq θ hθ t n]
  exact lemma56_actual_zero_removed_higher_logDeriv_bound θ hθ n

theorem lemma56_actual_normalized_logDeriv_remainder_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction θ)) (lemma55JensenCenter t) -
      iteratedDeriv n (lemma56LocalZeroLogDerivative θ t) (lemma55JensenCenter t)‖ /
        (n.factorial : ℝ) ≤
          450 * ((n : ℝ) + 1) * lemma56JensenLogSize θ t * (8 / 9 : ℝ) ^ (n + 1) := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
  calc
    _ ≤ (n + 1).factorial * (450 * lemma56JensenLogSize θ t) / (9 / 8 : ℝ) ^ (n + 1) :=
      lemma56_actual_higher_logDeriv_remainder_bound θ hθ n
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        div_eq_mul_inv, ← inv_pow, inv_div]
      ring

theorem lemma56_actual_logDeriv_remainder_sum_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} (S : Finset ℕ) :
    (∑ n ∈ S,
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction θ)) (lemma55JensenCenter t) -
        iteratedDeriv n (lemma56LocalZeroLogDerivative θ t) (lemma55JensenCenter t)‖ /
          (n.factorial : ℝ)) ≤ 32400 * lemma56JensenLogSize θ t := by
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
  have hLp : 0 < lemma56JensenLogSize θ t := lemma56_jensen_log_size_pos θ t
  calc
    _ ≤ ∑ n ∈ S, (400 * lemma56JensenLogSize θ t) * (((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n) := by
      apply Finset.sum_le_sum
      intro n _
      have hb := lemma56_actual_normalized_logDeriv_remainder_bound θ hθ (t := t) n
      apply hb.trans_eq
      rw [pow_succ]
      ring
    _ = (400 * lemma56JensenLogSize θ t) * ∑ n ∈ S, ((n : ℝ) + 1) * (8 / 9 : ℝ) ^ n := by
      rw [Finset.mul_sum]
    _ ≤ (400 * lemma56JensenLogSize θ t) * 81 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 32400 * lemma56JensenLogSize θ t := by ring

end ZhangLS.Spec
