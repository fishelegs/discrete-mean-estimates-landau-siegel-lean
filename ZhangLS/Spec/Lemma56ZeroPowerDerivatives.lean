import ZhangLS.Spec.Lemma56HigherLogDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-! # Exact actual inverse-power formulas and summable remainders

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

noncomputable def lemma56LocalZeroPowerSum {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (t : ℝ) (k : ℕ) : ℂ :=
  ∑ ρ ∈ lemma56LocalZeroFinset θ t,
    (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) /
      (lemma55JensenCenter t - ρ) ^ k

theorem lemma56_actual_local_zero_higher_derivative
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (lemma56LocalZeroLogDerivative θ t) (lemma55JensenCenter t) =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * lemma56LocalZeroPowerSum θ t (n + 1) := by
  classical
  have hne : ∀ ρ ∈ lemma56LocalZeroFinset θ t, lemma55JensenCenter t - ρ ≠ 0 := by
    intro ρ hρ hzero
    apply lemma56_actual_jensen_center_ne_zero θ t
    rw [sub_eq_zero.mp hzero]
    exact ((lemma56_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).2
  have ha : ∀ ρ ∈ lemma56LocalZeroFinset θ t,
      ContDiffAt ℂ n (fun w : ℂ =>
        (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) / (w - ρ))
          (lemma55JensenCenter t) := by
    intro ρ hρ
    exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hne ρ hρ)).contDiffAt
  unfold lemma56LocalZeroLogDerivative lemma56LocalZeroPowerSum
  rw [iteratedDeriv_fun_sum ha, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [lemma55_iterated_deriv_weighted_inverse_pole]
  have he : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, div_eq_mul_inv]
  ring

theorem lemma56_actual_power_sum_remainder_norm_eq
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (t : ℝ) (n : ℕ) :
    ‖lemma56NormalizedDerivative θ t n - lemma56LocalZeroPowerSum θ t (n + 1)‖ =
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction θ)) (lemma55JensenCenter t) -
        iteratedDeriv n (lemma56LocalZeroLogDerivative θ t) (lemma55JensenCenter t)‖ /
          (n.factorial : ℝ) := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hid : lemma56NormalizedDerivative θ t n - lemma56LocalZeroPowerSum θ t (n + 1) =
      ((-1 : ℂ) ^ n / (n.factorial : ℂ)) *
        (iteratedDeriv n (logDeriv (DirichletCharacter.LFunction θ)) (lemma55JensenCenter t) -
          iteratedDeriv n (lemma56LocalZeroLogDerivative θ t) (lemma55JensenCenter t)) := by
    rw [lemma56_actual_local_zero_higher_derivative θ hθ t n]
    unfold lemma56NormalizedDerivative
    field_simp
    linear_combination (lemma56LocalZeroPowerSum θ t (n + 1) * (n.factorial : ℂ)) * he
  rw [hid, norm_mul, norm_div, norm_pow]
  simp only [norm_neg, norm_one, one_pow, norm_natCast]
  ring

theorem lemma56_actual_power_sum_remainder_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {t : ℝ} (n : ℕ) :
    ‖lemma56NormalizedDerivative θ t n - lemma56LocalZeroPowerSum θ t (n + 1)‖ ≤
      450 * ((n : ℝ) + 1) * lemma56JensenLogSize θ t * (8 / 9 : ℝ) ^ (n + 1) := by
  rw [lemma56_actual_power_sum_remainder_norm_eq θ hθ t n]
  exact lemma56_actual_normalized_logDeriv_remainder_bound θ hθ n

theorem lemma56_actual_power_sum_remainder_sum_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {t : ℝ} (S : Finset ℕ) :
    (∑ n ∈ S,
      ‖lemma56NormalizedDerivative θ t n - lemma56LocalZeroPowerSum θ t (n + 1)‖) ≤
        32400 * lemma56JensenLogSize θ t := by
  simp_rw [lemma56_actual_power_sum_remainder_norm_eq θ hθ t]
  exact lemma56_actual_logDeriv_remainder_sum_bound θ hθ S

end ZhangLS.Spec
