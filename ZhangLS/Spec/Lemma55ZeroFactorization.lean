import ZhangLS.Spec.Lemma55ActualLocalZeros

/-!
# Removing exactly the actual local zeros

The finite local divisor defines a factor made from actual zero orders.
The quotient is put in meromorphic normal form at its removable singularities.
It is entire, nonzero on the whole closed local disk, and multiplies back
to the actual L-function everywhere, including the removed zeros.
-/

namespace ZhangLS.Spec

open Complex Metric Set Filter MeromorphicOn
open scoped Topology Real

noncomputable def lemma55LocalZeroFactor {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) : ℂ → ℂ :=
  ∏ᶠ ρ : ℂ, (· - ρ) ^ divisor (dirichletLFunction χ)
    (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) ρ

noncomputable def lemma55ZeroRemovedL {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) : ℂ → ℂ :=
  toMeromorphicNFOn (dirichletLFunction χ / lemma55LocalZeroFactor χ t) univ

theorem lemma55_actual_meromorphic_order_eq_nat
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (z : ℂ) :
    meromorphicOrderAt (dirichletLFunction χ) z =
      ((analyticOrderNatAt (dirichletLFunction χ) z : ℤ) : WithTop ℤ) := by
  rw [(lemma55_actual_L_analyticOnNhd χ hD z (mem_univ z)).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (lemma55_actual_analytic_order_finite χ hD z)]
  simp

theorem lemma55_actual_zero_factor_analytic
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    AnalyticOnNhd ℂ (lemma55LocalZeroFactor χ t) univ := by
  intro z _
  exact Function.FactorizedRational.analyticAt
    (((lemma55_actual_L_analyticOnNhd χ hD).mono (subset_univ _)).divisor_nonneg z)

theorem lemma55_actual_zero_factor_order
    {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) (z : ℂ) :
    meromorphicOrderAt (lemma55LocalZeroFactor χ t) z =
      (divisor (dirichletLFunction χ)
        (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) z : WithTop ℤ) :=
  Function.FactorizedRational.meromorphicOrderAt_eq _
    ((divisor (dirichletLFunction χ)
      (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))).finiteSupport
        (isCompact_closedBall _ _))

theorem lemma55_actual_zero_removed_order
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (z : ℂ) :
    meromorphicOrderAt (lemma55ZeroRemovedL χ t) z =
      (((analyticOrderNatAt (dirichletLFunction χ) z : ℤ) -
        divisor (dirichletLFunction χ)
          (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) z : ℤ) : WithTop ℤ) := by
  have hmer : MeromorphicOn (dirichletLFunction χ / lemma55LocalZeroFactor χ t) univ :=
    (lemma55_actual_L_analyticOnNhd χ hD).meromorphicOn.div
      (lemma55_actual_zero_factor_analytic χ hD t).meromorphicOn
  rw [lemma55ZeroRemovedL, meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z),
    meromorphicOrderAt_div
      ((lemma55_actual_L_analyticOnNhd χ hD z (mem_univ z)).meromorphicAt)
      ((lemma55_actual_zero_factor_analytic χ hD t z (mem_univ z)).meromorphicAt),
    lemma55_actual_meromorphic_order_eq_nat χ hD z,
    lemma55_actual_zero_factor_order χ t z,
    WithTop.LinearOrderedAddCommGroup.coe_sub]

theorem lemma55_actual_zero_removed_analytic
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    AnalyticOnNhd ℂ (lemma55ZeroRemovedL χ t) univ := by
  intro z _
  apply (meromorphicNFOn_toMeromorphicNFOn _ univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  change 0 ≤ meromorphicOrderAt (lemma55ZeroRemovedL χ t) z
  rw [lemma55_actual_zero_removed_order χ hD t z]
  by_cases hz : z ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)
  · rw [lemma55_actual_local_divisor_eq_order χ hD hz]
    simp
  · simp [hz]

theorem lemma55_actual_zero_removed_ne_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) :
    lemma55ZeroRemovedL χ t z ≠ 0 := by
  apply (meromorphicNFOn_toMeromorphicNFOn _ univ (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp
  change meromorphicOrderAt (lemma55ZeroRemovedL χ t) z = 0
  rw [lemma55_actual_zero_removed_order χ hD t z,
    lemma55_actual_local_divisor_eq_order χ hD hz]
  simp

theorem lemma55_actual_zero_removed_eq_quotient
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {t : ℝ} {z : ℂ}
    (hP : lemma55LocalZeroFactor χ t z ≠ 0) :
    lemma55ZeroRemovedL χ t z = dirichletLFunction χ z / lemma55LocalZeroFactor χ t z := by
  have hmer : MeromorphicOn (dirichletLFunction χ / lemma55LocalZeroFactor χ t) univ :=
    (lemma55_actual_L_analyticOnNhd χ hD).meromorphicOn.div
      (lemma55_actual_zero_factor_analytic χ hD t).meromorphicOn
  have ha := (lemma55_actual_L_analyticOnNhd χ hD z (mem_univ z)).div
    (lemma55_actual_zero_factor_analytic χ hD t z (mem_univ z)) hP
  rw [lemma55ZeroRemovedL, toMeromorphicNFOn_eq_toMeromorphicNFAt hmer (mem_univ z),
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
  rfl

theorem lemma55_actual_zero_factorization
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (z : ℂ) :
    dirichletLFunction χ z = lemma55LocalZeroFactor χ t z * lemma55ZeroRemovedL χ t z := by
  by_cases hP : lemma55LocalZeroFactor χ t z = 0
  · let d := divisor (dirichletLFunction χ)
      (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))
    have hd : d z ≠ 0 := by
      intro hd0
      exact Function.FactorizedRational.ne_zero hd0 hP
    have hz := d.supportWithinDomain hd
    have hn : analyticOrderNatAt (dirichletLFunction χ) z ≠ 0 := by
      intro hn0
      have heq := lemma55_actual_local_divisor_eq_order χ hD hz
      rw [hn0, Nat.cast_zero] at heq
      exact hd heq
    rw [apply_eq_zero_of_analyticOrderNatAt_ne_zero hn, hP, zero_mul]
  · rw [lemma55_actual_zero_removed_eq_quotient χ hD hP]
    exact (mul_div_cancel₀ (dirichletLFunction χ z) hP).symm

end ZhangLS.Spec
