import ZhangLS.Spec.Lemma59LocalZeroBudgets
import ZhangLS.Spec.Lemma56ZeroRemovedLog

/-! # Actual zero factors and zero-removed L-function bounds for Lemma 5.9

The exact actual L-function, divisor and analytic multiplicities are retained.
The full original Lemma 5.9 quotient is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma59LocalZeroFactor {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ → ℂ :=
  ∏ᶠ ρ : ℂ, (· - ρ) ^ divisor (DirichletCharacter.LFunction θ)
    (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) ρ

noncomputable def lemma59ZeroRemovedL {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ → ℂ :=
  toMeromorphicNFOn (DirichletCharacter.LFunction θ / lemma59LocalZeroFactor θ t) univ

theorem lemma59_actual_meromorphic_order_eq_nat
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (z : ℂ) :
    meromorphicOrderAt (DirichletCharacter.LFunction θ) z =
      ((analyticOrderNatAt (DirichletCharacter.LFunction θ) z : ℤ) : WithTop ℤ) := by
  rw [(lemma56_actual_L_analyticOnNhd θ hθ z (mem_univ z)).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (lemma56_actual_analytic_order_finite θ hθ z)]
  simp

theorem lemma59_actual_zero_factor_analytic
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    AnalyticOnNhd ℂ (lemma59LocalZeroFactor θ t) univ := by
  intro z _
  exact Function.FactorizedRational.analyticAt
    (((lemma56_actual_L_analyticOnNhd θ hθ).mono (subset_univ _)).divisor_nonneg z)

theorem lemma59_actual_zero_factor_order
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (t : ℝ) (z : ℂ) :
    meromorphicOrderAt (lemma59LocalZeroFactor θ t) z =
      (divisor (DirichletCharacter.LFunction θ)
        (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) z : WithTop ℤ) :=
  Function.FactorizedRational.meromorphicOrderAt_eq _
    ((divisor (DirichletCharacter.LFunction θ)
      (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ))).finiteSupport
        (isCompact_closedBall _ _))

theorem lemma59_actual_zero_removed_order
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (z : ℂ) :
    meromorphicOrderAt (lemma59ZeroRemovedL θ t) z =
      (((analyticOrderNatAt (DirichletCharacter.LFunction θ) z : ℤ) -
        divisor (DirichletCharacter.LFunction θ)
          (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) z : ℤ) : WithTop ℤ) := by
  have hmer : MeromorphicOn (DirichletCharacter.LFunction θ / lemma59LocalZeroFactor θ t) univ :=
    (lemma56_actual_L_analyticOnNhd θ hθ).meromorphicOn.div
      (lemma59_actual_zero_factor_analytic θ hθ t).meromorphicOn
  rw [lemma59ZeroRemovedL, meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z),
    meromorphicOrderAt_div
      ((lemma56_actual_L_analyticOnNhd θ hθ z (mem_univ z)).meromorphicAt)
      ((lemma59_actual_zero_factor_analytic θ hθ t z (mem_univ z)).meromorphicAt),
    lemma59_actual_meromorphic_order_eq_nat θ hθ z,
    lemma59_actual_zero_factor_order θ t z,
    WithTop.LinearOrderedAddCommGroup.coe_sub]

theorem lemma59_actual_zero_removed_analytic
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    AnalyticOnNhd ℂ (lemma59ZeroRemovedL θ t) univ := by
  intro z _
  apply (meromorphicNFOn_toMeromorphicNFOn _ univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  change 0 ≤ meromorphicOrderAt (lemma59ZeroRemovedL θ t) z
  rw [lemma59_actual_zero_removed_order θ hθ t z]
  by_cases hz : z ∈ closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)
  · rw [lemma59_actual_local_divisor_eq_order θ hθ hz]
    simp
  · simp [hz]

theorem lemma59_actual_zero_removed_ne_zero
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) :
    lemma59ZeroRemovedL θ t z ≠ 0 := by
  apply (meromorphicNFOn_toMeromorphicNFOn _ univ (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp
  change meromorphicOrderAt (lemma59ZeroRemovedL θ t) z = 0
  rw [lemma59_actual_zero_removed_order θ hθ t z,
    lemma59_actual_local_divisor_eq_order θ hθ hz]
  simp

theorem lemma59_actual_zero_removed_eq_quotient
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hP : lemma59LocalZeroFactor θ t z ≠ 0) :
    lemma59ZeroRemovedL θ t z = DirichletCharacter.LFunction θ z / lemma59LocalZeroFactor θ t z := by
  have hmer : MeromorphicOn (DirichletCharacter.LFunction θ / lemma59LocalZeroFactor θ t) univ :=
    (lemma56_actual_L_analyticOnNhd θ hθ).meromorphicOn.div
      (lemma59_actual_zero_factor_analytic θ hθ t).meromorphicOn
  have ha := (lemma56_actual_L_analyticOnNhd θ hθ z (mem_univ z)).div
    (lemma59_actual_zero_factor_analytic θ hθ t z (mem_univ z)) hP
  rw [lemma59ZeroRemovedL, toMeromorphicNFOn_eq_toMeromorphicNFAt hmer (mem_univ z),
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
  rfl

theorem lemma59_actual_zero_factorization
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (z : ℂ) :
    DirichletCharacter.LFunction θ z = lemma59LocalZeroFactor θ t z * lemma59ZeroRemovedL θ t z := by
  by_cases hP : lemma59LocalZeroFactor θ t z = 0
  · let d := divisor (DirichletCharacter.LFunction θ)
      (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ))
    have hd : d z ≠ 0 := by
      intro hd0
      exact Function.FactorizedRational.ne_zero hd0 hP
    have hz := d.supportWithinDomain hd
    have hn : analyticOrderNatAt (DirichletCharacter.LFunction θ) z ≠ 0 := by
      intro hn0
      have heq := lemma59_actual_local_divisor_eq_order θ hθ hz
      rw [hn0, Nat.cast_zero] at heq
      exact hd heq
    rw [apply_eq_zero_of_analyticOrderNatAt_ne_zero hn, hP, zero_mul]
  · rw [lemma59_actual_zero_removed_eq_quotient θ hθ hP]
    exact (mul_div_cancel₀ (DirichletCharacter.LFunction θ z) hP).symm

end ZhangLS.Spec
