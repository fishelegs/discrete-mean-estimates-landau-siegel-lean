import ZhangLS.Spec.Lemma59ZeroFactorization

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

noncomputable def lemma59LocalMultiplicity {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℕ :=
  ∑ ρ ∈ lemma59LocalZeroFinset θ t, analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ

theorem lemma59_actual_zero_factor_eq_product
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (z : ℂ) :
    lemma59LocalZeroFactor θ t z =
      ∏ ρ ∈ lemma59LocalZeroFinset θ t, (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ := by
  classical
  unfold lemma59LocalZeroFactor
  rw [finprod_eq_prod_of_mulSupport_subset (s := lemma59LocalZeroFinset θ t)]
  · rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro ρ hρ
    rw [lemma59_actual_local_divisor_eq_order θ hθ
      ((lemma59_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).1]
    simp
  · rw [Function.FactorizedRational.mulSupport]
    simp [lemma59LocalZeroFinset]

theorem lemma59_actual_local_multiplicity_eq_count
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (lemma59LocalMultiplicity θ t : ℤ) = lemma59JensenMultiplicityCount θ t := by
  rw [lemma59_actual_multiplicity_count_eq_sum_orders θ hθ t]
  simp [lemma59LocalMultiplicity]

theorem lemma59_actual_zero_factor_center_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    ‖lemma59LocalZeroFactor θ t (lemma55JensenCenter t)‖ ≤
      (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t := by
  classical
  rw [lemma59_actual_zero_factor_eq_product θ hθ t, norm_prod]
  calc
    _ ≤ ∏ ρ ∈ lemma59LocalZeroFinset θ t,
        (7 / 4 : ℝ) ^ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        positivity
      · intro ρ hρ
        rw [norm_pow]
        apply pow_le_pow_left₀ (norm_nonneg _)
        have hb := ((lemma59_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).1
        rw [mem_closedBall_iff_norm, norm_sub_rev] at hb
        exact hb
    _ = (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t :=
      Finset.prod_pow_eq_pow_sum _ _ _

theorem lemma59_actual_zero_factor_outer_lower_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (15 / 8 : ℝ)) :
    (1 / 8 : ℝ) ^ lemma59LocalMultiplicity θ t ≤ ‖lemma59LocalZeroFactor θ t z‖ := by
  classical
  rw [lemma59_actual_zero_factor_eq_product θ hθ t, norm_prod]
  rw [lemma59LocalMultiplicity, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro ρ _
    positivity
  · intro ρ hρ
    rw [norm_pow]
    apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hr := ((lemma59_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).1
    have hdρ : ‖ρ - lemma55JensenCenter t‖ ≤ (7 : ℝ) / 4 := mem_closedBall_iff_norm.mp hr
    have hdz : ‖z - lemma55JensenCenter t‖ = (15 : ℝ) / 8 := mem_sphere_iff_norm.mp hz
    have htri := norm_add_le (z - ρ) (ρ - lemma55JensenCenter t)
    rw [sub_add_sub_cancel, hdz] at htri
    linarith only [htri, hdρ]

theorem lemma59_actual_zero_factor_outer_ne_zero
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (15 / 8 : ℝ)) :
    lemma59LocalZeroFactor θ t z ≠ 0 := by
  have hb := lemma59_actual_zero_factor_outer_lower_bound θ hθ hz
  have hp : 0 < (1 / 8 : ℝ) ^ lemma59LocalMultiplicity θ t := by positivity
  exact norm_pos_iff.mp (hp.trans_le hb)

theorem lemma59_actual_local_multiplicity_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (lemma59LocalMultiplicity θ t : ℝ) ≤
      15 * Real.log (32 * (r : ℝ) * (4 + |t|)) := by
  have hb := lemma59_actual_large_disk_multiplicity_bound θ hθ t
  rw [← lemma59_actual_local_multiplicity_eq_count θ hθ t] at hb
  exact_mod_cast hb

end ZhangLS.Spec
