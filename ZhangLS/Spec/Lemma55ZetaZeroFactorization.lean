import ZhangLS.Spec.Lemma55ZetaLocalZeros

/-!
# Actual local zeta factorization on the right half-plane

The factor contains exactly the local actual zeta zeros. The quotient
is filled at its removable values with meromorphic normal form. Its
analyticity and the pointwise product identity include removed zeros.
All disks used later lie inside this proved right-half-plane domain.
-/

namespace ZhangLS.Spec

open Complex Metric Set Filter MeromorphicOn
open scoped Topology

noncomputable def lemma55ZetaLocalZeroFactor (t : ℝ) : ℂ → ℂ :=
  ∏ᶠ ρ : ℂ, (· - ρ) ^ divisor zetaPoleRemoved
    (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) ρ

noncomputable def lemma55ZetaZeroRemoved (t : ℝ) : ℂ → ℂ :=
  toMeromorphicNFOn (zetaPoleRemoved / lemma55ZetaLocalZeroFactor t) lemma55ZetaRightHalfPlane

theorem lemma55_actual_zeta_removed_meromorphic_order {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt zetaPoleRemoved z =
      ((analyticOrderNatAt zetaPoleRemoved z : ℤ) : WithTop ℤ) := by
  rw [(lemma55_actual_zeta_pole_removed_analyticAt hz).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (lemma55_actual_zeta_pole_removed_order_finite hz)]
  simp

theorem lemma55_actual_zeta_zero_factor_analytic (t : ℝ) :
    AnalyticOnNhd ℂ (lemma55ZetaLocalZeroFactor t) univ := by
  intro z _
  exact Function.FactorizedRational.analyticAt
    ((lemma55_actual_zeta_disk_analytic t (5 / 4) (by norm_num)).divisor_nonneg z)

theorem lemma55_actual_zeta_zero_factor_order (t : ℝ) (z : ℂ) :
    meromorphicOrderAt (lemma55ZetaLocalZeroFactor t) z =
      (divisor zetaPoleRemoved (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) z : WithTop ℤ) :=
  Function.FactorizedRational.meromorphicOrderAt_eq _
    ((divisor zetaPoleRemoved (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))).finiteSupport
      (isCompact_closedBall _ _))

theorem lemma55_actual_zeta_zero_removed_order (t : ℝ) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (lemma55ZetaZeroRemoved t) z =
      (((analyticOrderNatAt zetaPoleRemoved z : ℤ) -
        divisor zetaPoleRemoved (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) z : ℤ) : WithTop ℤ) := by
  have hmer : MeromorphicOn (zetaPoleRemoved / lemma55ZetaLocalZeroFactor t) lemma55ZetaRightHalfPlane :=
    lemma55_actual_zeta_right_analytic.meromorphicOn.div
      ((lemma55_actual_zeta_zero_factor_analytic t).mono (subset_univ _)).meromorphicOn
  rw [lemma55ZetaZeroRemoved, meromorphicOrderAt_toMeromorphicNFOn hmer hz,
    meromorphicOrderAt_div (lemma55_actual_zeta_pole_removed_analyticAt hz).meromorphicAt
      (lemma55_actual_zeta_zero_factor_analytic t z (mem_univ z)).meromorphicAt,
    lemma55_actual_zeta_removed_meromorphic_order hz, lemma55_actual_zeta_zero_factor_order t z,
    WithTop.LinearOrderedAddCommGroup.coe_sub]

theorem lemma55_actual_zeta_zero_removed_analytic (t : ℝ) :
    AnalyticOnNhd ℂ (lemma55ZetaZeroRemoved t) lemma55ZetaRightHalfPlane := by
  intro z hz
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (zetaPoleRemoved / lemma55ZetaLocalZeroFactor t) lemma55ZetaRightHalfPlane hz
  apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  change 0 ≤ meromorphicOrderAt (lemma55ZetaZeroRemoved t) z
  rw [lemma55_actual_zeta_zero_removed_order t hz]
  by_cases hball : z ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)
  · rw [lemma55_actual_zeta_local_divisor_eq_order hball]
    simp
  · simp [hball]

theorem lemma55_actual_zeta_zero_removed_ne_zero {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) :
    lemma55ZetaZeroRemoved t z ≠ 0 := by
  have hp := lemma55_zeta_disk_re_pos (by norm_num) hz
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (zetaPoleRemoved / lemma55ZetaLocalZeroFactor t) lemma55ZetaRightHalfPlane hp
  apply hnf.meromorphicOrderAt_eq_zero_iff.mp
  change meromorphicOrderAt (lemma55ZetaZeroRemoved t) z = 0
  rw [lemma55_actual_zeta_zero_removed_order t hp, lemma55_actual_zeta_local_divisor_eq_order hz]
  simp

theorem lemma55_actual_zeta_zero_removed_eq_quotient {t : ℝ} {z : ℂ} (hz : 0 < z.re)
    (hP : lemma55ZetaLocalZeroFactor t z ≠ 0) :
    lemma55ZetaZeroRemoved t z = zetaPoleRemoved z / lemma55ZetaLocalZeroFactor t z := by
  have hmer : MeromorphicOn (zetaPoleRemoved / lemma55ZetaLocalZeroFactor t) lemma55ZetaRightHalfPlane :=
    lemma55_actual_zeta_right_analytic.meromorphicOn.div
      ((lemma55_actual_zeta_zero_factor_analytic t).mono (subset_univ _)).meromorphicOn
  have ha := (lemma55_actual_zeta_pole_removed_analyticAt hz).div
    (lemma55_actual_zeta_zero_factor_analytic t z (mem_univ z)) hP
  rw [lemma55ZetaZeroRemoved, toMeromorphicNFOn_eq_toMeromorphicNFAt hmer hz,
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
  rfl

theorem lemma55_actual_zeta_zero_factorization (t : ℝ) {z : ℂ} (hz : 0 < z.re) :
    zetaPoleRemoved z = lemma55ZetaLocalZeroFactor t z * lemma55ZetaZeroRemoved t z := by
  by_cases hP : lemma55ZetaLocalZeroFactor t z = 0
  · let d := divisor zetaPoleRemoved (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))
    have hd : d z ≠ 0 := by
      intro hd0
      exact Function.FactorizedRational.ne_zero hd0 hP
    have hball := d.supportWithinDomain hd
    have hn : analyticOrderNatAt zetaPoleRemoved z ≠ 0 := by
      intro hn0
      have heq := lemma55_actual_zeta_local_divisor_eq_order hball
      rw [hn0, Nat.cast_zero] at heq
      exact hd heq
    rw [apply_eq_zero_of_analyticOrderNatAt_ne_zero hn, hP, zero_mul]
  · rw [lemma55_actual_zeta_zero_removed_eq_quotient hz hP]
    exact (mul_div_cancel₀ (zetaPoleRemoved z) hP).symm

end ZhangLS.Spec
