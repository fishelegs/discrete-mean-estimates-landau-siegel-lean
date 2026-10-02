import ZhangLS.Spec.Lemma56ZeroFactorBounds
import Mathlib.Analysis.Complex.AbsMax

/-! # Actual zero-removed function and normalized ratio bounds

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

theorem lemma56_actual_zero_removed_outer_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma56ZeroRemovedL θ t z‖ ≤
      2 * (r : ℝ) * (7 / 2 + |t|) * (4 : ℝ) ^ lemma56LocalMultiplicity θ t := by
  have hP := lemma56_actual_zero_factor_outer_ne_zero θ hθ hz
  have hp := lemma56_actual_zero_factor_outer_lower_bound θ hθ hz
  have hinv : ‖lemma56LocalZeroFactor θ t z‖⁻¹ ≤
      (4 : ℝ) ^ lemma56LocalMultiplicity θ t := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (1 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t) hp
    simpa [one_div_pow, one_div] using h
  rw [lemma56_actual_zero_removed_eq_quotient θ hθ hP, norm_div, div_eq_mul_inv]
  exact mul_le_mul
    (lemma56_actual_jensen_disk_bound θ hθ (sphere_subset_closedBall hz)) hinv
    (by positivity) (by positivity)

theorem lemma56_actual_zero_removed_closed_disk_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma56ZeroRemovedL θ t z‖ ≤
      2 * (r : ℝ) * (7 / 2 + |t|) * (4 : ℝ) ^ lemma56LocalMultiplicity θ t := by
  have hd : Differentiable ℂ (lemma56ZeroRemovedL θ t) := fun z =>
    (lemma56_actual_zero_removed_analytic θ hθ t z (mem_univ z)).differentiableAt
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball)
    hd.diffContOnCl
  · intro w hw
    rw [frontier_ball (lemma55JensenCenter t) (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hw
    exact lemma56_actual_zero_removed_outer_bound θ hθ hw
  · rw [closure_ball (lemma55JensenCenter t) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    exact hz

theorem lemma56_actual_zero_removed_center_lower_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t) ≤
      ‖lemma56ZeroRemovedL θ t (lemma55JensenCenter t)‖ := by
  have hL := lemma56_actual_jensen_center_lower_bound θ t
  rw [lemma56_actual_zero_factorization θ hθ t (lemma55JensenCenter t), norm_mul] at hL
  have hP := lemma56_actual_zero_factor_center_bound θ hθ t
  have hprod := mul_le_mul_of_nonneg_right hP
    (norm_nonneg (lemma56ZeroRemovedL θ t (lemma55JensenCenter t)))
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hL, hprod]

noncomputable def lemma56JensenLogSize {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℝ :=
  Real.log (8 * (r : ℝ) * (7 / 2 + |t|))

noncomputable def lemma56ZeroRemovedRatioBound {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℝ :=
  8 * (r : ℝ) * (7 / 2 + |t|) * (5 : ℝ) ^ lemma56LocalMultiplicity θ t

lemma lemma56_jensen_log_size_pos {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : 0 < lemma56JensenLogSize θ t := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  apply Real.log_pos
  nlinarith only [hr1, abs_nonneg t]

theorem lemma56_zero_removed_ratio_bound_gt_one
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (t : ℝ) :
    1 < lemma56ZeroRemovedRatioBound θ t := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hpow : (1 : ℝ) ≤ 5 ^ lemma56LocalMultiplicity θ t := one_le_pow₀ (by norm_num)
  have hX : 1 < 8 * (r : ℝ) * (7 / 2 + |t|) := by nlinarith only [hr1, abs_nonneg t]
  unfold lemma56ZeroRemovedRatioBound
  nlinarith only [hX, hpow]

theorem lemma56_actual_zero_removed_ratio_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma56ZeroRemovedL θ t z /
      lemma56ZeroRemovedL θ t (lemma55JensenCenter t)‖ ≤
        lemma56ZeroRemovedRatioBound θ t := by
  have hc := lemma56_actual_zero_removed_center_lower_bound θ hθ t
  have hcp : 0 < ‖lemma56ZeroRemovedL θ t (lemma55JensenCenter t)‖ :=
    (by positivity : 0 < (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t)).trans_le hc
  have hinv : ‖lemma56ZeroRemovedL θ t (lemma55JensenCenter t)‖⁻¹ ≤
      4 * (5 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t)) hc
    simpa [one_div] using h
  rw [norm_div, div_eq_mul_inv]
  calc
    _ ≤ (2 * (r : ℝ) * (7 / 2 + |t|) * (4 : ℝ) ^ lemma56LocalMultiplicity θ t) *
        (4 * (5 / 4 : ℝ) ^ lemma56LocalMultiplicity θ t) :=
      mul_le_mul (lemma56_actual_zero_removed_closed_disk_bound θ hθ hz) hinv
        (by positivity) (by positivity)
    _ = lemma56ZeroRemovedRatioBound θ t := by
      unfold lemma56ZeroRemovedRatioBound
      rw [show (5 / 4 : ℝ) = 5 * 4⁻¹ by norm_num, mul_pow, inv_pow]
      have h4 : (4 : ℝ) ^ lemma56LocalMultiplicity θ t ≠ 0 := by positivity
      field_simp
      ring

theorem lemma56_actual_zero_removed_log_ratio_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    Real.log (lemma56ZeroRemovedRatioBound θ t) ≤ 25 * lemma56JensenLogSize θ t := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hN := lemma56_actual_local_multiplicity_bound θ hθ t
  have h5 : Real.log (5 : ℝ) ≤ 4 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
  unfold lemma56ZeroRemovedRatioBound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hmul := mul_le_mul_of_nonneg_left h5
    (Nat.cast_nonneg (lemma56LocalMultiplicity θ t) : (0 : ℝ) ≤ _)
  change Real.log (8 * (r : ℝ) * (7 / 2 + |t|)) + _ ≤ _
  dsimp [lemma56JensenLogSize]
  nlinarith only [hN, hmul]

end ZhangLS.Spec
