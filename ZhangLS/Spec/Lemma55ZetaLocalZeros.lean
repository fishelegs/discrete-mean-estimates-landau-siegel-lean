import ZhangLS.Spec.Lemma55ZetaLocalData

/-!
# Exact actual zeta zeros and multiplicities in the local closed disks

The pole-removed factor has value one at s=1. Its finite divisor support
is exactly the actual zeta zero set in the closed radius-5/4 disk. At
every such zero its analytic order equals the actual zeta order.
-/

namespace ZhangLS.Spec

open Complex Metric Set Filter MeromorphicOn
open scoped Topology

def lemma55ZetaRightHalfPlane : Set ℂ := {z | 0 < z.re}

theorem lemma55_actual_zeta_right_analytic :
    AnalyticOnNhd ℂ zetaPoleRemoved lemma55ZetaRightHalfPlane :=
  fun _ hz => lemma55_actual_zeta_pole_removed_analyticAt hz

lemma lemma55_zeta_disk_re_pos {t : ℝ} {z : ℂ} {R : ℝ}
    (hR : R ≤ 3 / 2) (hz : z ∈ closedBall (lemma55JensenCenter t) R) : 0 < z.re := by
  have hr := lemma55_jensen_disk_re_lower_bound (closedBall_subset_closedBall hR hz)
  linarith only [hr]

theorem lemma55_actual_zeta_disk_analytic (t R : ℝ) (hR : R ≤ 3 / 2) :
    AnalyticOnNhd ℂ zetaPoleRemoved (closedBall (lemma55JensenCenter t) R) :=
  fun _ hz => lemma55_actual_zeta_pole_removed_analyticAt (lemma55_zeta_disk_re_pos hR hz)

theorem lemma55_actual_zeta_order_eq_removed {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    analyticOrderAt zetaPoleRemoved z = analyticOrderAt riemannZeta z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have heq : zetaPoleRemoved =ᶠ[𝓝 z] (fun w : ℂ => w - 1) * riemannZeta := by
    filter_upwards [continuousAt_id.eventually_ne hz0, continuousAt_id.eventually_ne hz1] with w hw0 hw1
    exact zetaPoleRemoved_eq_mul_riemannZeta hw0 hw1
  have ha : AnalyticAt ℂ (fun w : ℂ => w - 1) z := analyticAt_id.sub analyticAt_const
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul ha (analyticOn_riemannZeta z hz1),
    ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz1), zero_add]

theorem lemma55_actual_zeta_order_nat_eq_removed {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    analyticOrderNatAt zetaPoleRemoved z = analyticOrderNatAt riemannZeta z := by
  unfold analyticOrderNatAt
  rw [lemma55_actual_zeta_order_eq_removed hz hz1]

noncomputable def lemma55ZetaLocalZeroFinset (t : ℝ) : Finset ℂ :=
  ((divisor zetaPoleRemoved (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))).finiteSupport
    (isCompact_closedBall _ _)).toFinset

theorem lemma55_actual_zeta_local_divisor_eq_order {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) :
    divisor zetaPoleRemoved (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) ρ =
      (analyticOrderNatAt zetaPoleRemoved ρ : ℤ) := by
  have ha := lemma55_actual_zeta_disk_analytic t (5 / 4) (by norm_num)
  rw [ha.divisor_apply hρ, ← Nat.cast_analyticOrderNatAt
    (lemma55_actual_zeta_pole_removed_order_finite (lemma55_zeta_disk_re_pos (by norm_num) hρ))]
  simp

theorem lemma55_mem_actual_zeta_local_zero_finset (t : ℝ) (ρ : ℂ) :
    ρ ∈ lemma55ZetaLocalZeroFinset t ↔
      ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) ∧ riemannZeta ρ = 0 := by
  classical
  let d := divisor zetaPoleRemoved (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))
  have hmem : ρ ∈ lemma55ZetaLocalZeroFinset t ↔ ρ ∈ Function.support d := by
    simp [lemma55ZetaLocalZeroFinset, d]
  rw [hmem]
  constructor
  · intro hsupp
    have hρ : ρ ∈ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) := d.supportWithinDomain hsupp
    have hn : analyticOrderNatAt zetaPoleRemoved ρ ≠ 0 := by
      intro hn0
      have heq := lemma55_actual_zeta_local_divisor_eq_order hρ
      rw [hn0, Nat.cast_zero] at heq
      exact hsupp heq
    exact ⟨hρ, (lemma55_actual_zeta_pole_removed_zero_iff
      (lemma55_zeta_disk_re_pos (by norm_num) hρ)).mp (apply_eq_zero_of_analyticOrderNatAt_ne_zero hn)⟩
  · rintro ⟨hρ, hζ⟩
    change d ρ ≠ 0
    dsimp [d]
    rw [lemma55_actual_zeta_local_divisor_eq_order hρ]
    have hp := lemma55_zeta_disk_re_pos (by norm_num) hρ
    have hn : analyticOrderNatAt zetaPoleRemoved ρ ≠ 0 := by
      intro hn0
      have ho : analyticOrderAt zetaPoleRemoved ρ = 0 := by
        rw [← Nat.cast_analyticOrderNatAt (lemma55_actual_zeta_pole_removed_order_finite hp), hn0]
        rfl
      exact ((lemma55_actual_zeta_pole_removed_analyticAt hp).analyticOrderAt_eq_zero.mp ho)
        ((lemma55_actual_zeta_pole_removed_zero_iff hp).mpr hζ)
    exact_mod_cast hn

theorem lemma55_actual_zeta_local_zero_order_nat_eq {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma55ZetaLocalZeroFinset t) :
    analyticOrderNatAt zetaPoleRemoved ρ = analyticOrderNatAt riemannZeta ρ := by
  have hz := (lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ
  have hne : ρ ≠ 1 := by intro h; exact riemannZeta_one_ne_zero (h ▸ hz.2)
  exact lemma55_actual_zeta_order_nat_eq_removed (lemma55_zeta_disk_re_pos (by norm_num) hz.1) hne

theorem lemma55_actual_zeta_local_zero_order_pos {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma55ZetaLocalZeroFinset t) : 1 ≤ analyticOrderNatAt zetaPoleRemoved ρ := by
  have hz := (lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ
  have hp := lemma55_zeta_disk_re_pos (by norm_num) hz.1
  apply Nat.one_le_iff_ne_zero.mpr
  intro hn0
  have ho : analyticOrderAt zetaPoleRemoved ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt (lemma55_actual_zeta_pole_removed_order_finite hp), hn0]
    rfl
  exact ((lemma55_actual_zeta_pole_removed_analyticAt hp).analyticOrderAt_eq_zero.mp ho)
    ((lemma55_actual_zeta_pole_removed_zero_iff hp).mpr hz.2)

noncomputable def lemma55ZetaLocalMultiplicity (t : ℝ) : ℕ :=
  ∑ ρ ∈ lemma55ZetaLocalZeroFinset t, analyticOrderNatAt zetaPoleRemoved ρ

theorem lemma55_actual_zeta_local_multiplicity_eq_count (t : ℝ) :
    (lemma55ZetaLocalMultiplicity t : ℤ) = lemma55ZetaJensenMultiplicityCount t := by
  let d := divisor zetaPoleRemoved (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ))
  have heq : lemma55ZetaJensenMultiplicityCount t = ∑ ρ ∈ lemma55ZetaLocalZeroFinset t, d ρ :=
    finsum_eq_sum d (d.finiteSupport (isCompact_closedBall _ _))
  rw [heq]
  simp only [lemma55ZetaLocalMultiplicity, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  exact (lemma55_actual_zeta_local_divisor_eq_order
    ((lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ).1).symm

theorem lemma55_actual_zeta_local_multiplicity_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    (lemma55ZetaLocalMultiplicity t : ℝ) ≤ 18 * Real.log (D : ℝ) := by
  have h := lemma55_actual_zeta_jensen_multiplicity_bound hD hL ht
  rw [← lemma55_actual_zeta_local_multiplicity_eq_count t] at h
  exact_mod_cast h

end ZhangLS.Spec
