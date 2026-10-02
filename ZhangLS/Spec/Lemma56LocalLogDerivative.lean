import ZhangLS.Spec.Lemma56ZeroRemovedLog

/-! # Exact actual local logarithmic derivative formulas

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

theorem lemma56_actual_zero_factor_logDeriv
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hP : lemma56LocalZeroFactor θ t z ≠ 0) :
    logDeriv (lemma56LocalZeroFactor θ t) z =
      ∑ ρ ∈ lemma56LocalZeroFinset θ t,
        (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) / (z - ρ) := by
  classical
  have heq : lemma56LocalZeroFactor θ t = fun w =>
      ∏ ρ ∈ lemma56LocalZeroFinset θ t,
        (w - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ :=
    funext (lemma56_actual_zero_factor_eq_product θ hθ t)
  have hterms : ∀ ρ ∈ lemma56LocalZeroFinset θ t,
      (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mp
    rwa [← lemma56_actual_zero_factor_eq_product θ hθ t z]
  rw [heq, logDeriv_prod hterms (fun ρ _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro ρ _
  have hderiv : deriv (fun w : ℂ => w - ρ) z = 1 := by
    simpa using ((hasDerivAt_id z).sub_const ρ).deriv
  rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply, hderiv]
  ring

theorem lemma56_actual_local_logDeriv_formula
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) {z : ℂ}
    (hLz : DirichletCharacter.LFunction θ z ≠ 0) :
    logDeriv (DirichletCharacter.LFunction θ) z =
      (∑ ρ ∈ lemma56LocalZeroFinset θ t,
        (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) / (z - ρ)) +
          logDeriv (lemma56ZeroRemovedL θ t) z := by
  have heq : DirichletCharacter.LFunction θ = fun w =>
      lemma56LocalZeroFactor θ t w * lemma56ZeroRemovedL θ t w :=
    funext (lemma56_actual_zero_factorization θ hθ t)
  have hn : lemma56LocalZeroFactor θ t z ≠ 0 ∧ lemma56ZeroRemovedL θ t z ≠ 0 := by
    apply mul_ne_zero_iff.mp
    rwa [← lemma56_actual_zero_factorization θ hθ t z]
  nth_rw 1 [heq]
  rw [logDeriv_mul z hn.1 hn.2
    (lemma56_actual_zero_factor_analytic θ hθ t z (mem_univ z)).differentiableAt
    (lemma56_actual_zero_removed_analytic θ hθ t z (mem_univ z)).differentiableAt]
  rw [lemma56_actual_zero_factor_logDeriv θ hθ hn.1]

end ZhangLS.Spec
