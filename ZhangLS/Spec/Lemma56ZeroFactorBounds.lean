import ZhangLS.Spec.Lemma56ZeroFactorization

/-! # Actual zero-factor bounds on closed local disks

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

noncomputable def lemma56LocalMultiplicity {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℕ :=
  ∑ ρ ∈ lemma56LocalZeroFinset θ t, analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ

theorem lemma56_actual_zero_factor_eq_product
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (z : ℂ) :
    lemma56LocalZeroFactor θ t z =
      ∏ ρ ∈ lemma56LocalZeroFinset θ t, (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ := by
  classical
  unfold lemma56LocalZeroFactor
  rw [finprod_eq_prod_of_mulSupport_subset (s := lemma56LocalZeroFinset θ t)]
  · rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro ρ hρ
    rw [lemma56_actual_local_divisor_eq_order θ hθ
      ((lemma56_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).1]
    simp
  · rw [Function.FactorizedRational.mulSupport]
    simp [lemma56LocalZeroFinset]

theorem lemma56_actual_local_multiplicity_eq_count
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (lemma56LocalMultiplicity θ t : ℤ) = lemma56JensenMultiplicityCount θ t := by
  rw [lemma56_actual_multiplicity_count_eq_sum_orders θ hθ t]
  simp [lemma56LocalMultiplicity]

theorem lemma56_actual_zero_factor_center_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    ‖lemma56LocalZeroFactor θ t (lemma55JensenCenter t)‖ ≤
      (5 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t := by
  classical
  rw [lemma56_actual_zero_factor_eq_product θ hθ t, norm_prod]
  calc
    _ ≤ ∏ ρ ∈ lemma56LocalZeroFinset θ t,
        (5 / 4 : ℝ) ^ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        positivity
      · intro ρ hρ
        rw [norm_pow]
        apply pow_le_pow_left₀ (norm_nonneg _)
        have hb := ((lemma56_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).1
        rw [mem_closedBall_iff_norm, norm_sub_rev] at hb
        exact hb
    _ = (5 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t :=
      Finset.prod_pow_eq_pow_sum _ _ _

theorem lemma56_actual_zero_factor_outer_lower_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    (1 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t ≤ ‖lemma56LocalZeroFactor θ t z‖ := by
  classical
  rw [lemma56_actual_zero_factor_eq_product θ hθ t, norm_prod]
  rw [lemma56LocalMultiplicity, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro ρ _
    positivity
  · intro ρ hρ
    rw [norm_pow]
    apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hr := ((lemma56_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).1
    have hdρ : ‖ρ - lemma55JensenCenter t‖ ≤ (5 : ℝ) / 4 := mem_closedBall_iff_norm.mp hr
    have hdz : ‖z - lemma55JensenCenter t‖ = (3 : ℝ) / 2 := mem_sphere_iff_norm.mp hz
    have htri := norm_add_le (z - ρ) (ρ - lemma55JensenCenter t)
    rw [sub_add_sub_cancel, hdz] at htri
    linarith only [htri, hdρ]

theorem lemma56_actual_zero_factor_outer_ne_zero
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    lemma56LocalZeroFactor θ t z ≠ 0 := by
  have hb := lemma56_actual_zero_factor_outer_lower_bound θ hθ hz
  have hp : 0 < (1 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t := by positivity
  exact norm_pos_iff.mp (hp.trans_le hb)

theorem lemma56_actual_local_multiplicity_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (lemma56LocalMultiplicity θ t : ℝ) ≤
      6 * Real.log (8 * (r : ℝ) * (7 / 2 + |t|)) := by
  have hb := lemma56_actual_jensen_multiplicity_bound θ hθ t
  rw [← lemma56_actual_local_multiplicity_eq_count θ hθ t] at hb
  exact_mod_cast hb

end ZhangLS.Spec
