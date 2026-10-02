import ZhangLS.Spec.Lemma59ZeroFactorBounds
import Mathlib.Analysis.Complex.AbsMax

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

theorem lemma59_actual_zero_removed_outer_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (15 / 8 : ℝ)) :
    ‖lemma59ZeroRemovedL θ t z‖ ≤
      8 * (r : ℝ) * (4 + |t|) * (8 : ℝ) ^ lemma59LocalMultiplicity θ t := by
  have hP := lemma59_actual_zero_factor_outer_ne_zero θ hθ hz
  have hp := lemma59_actual_zero_factor_outer_lower_bound θ hθ hz
  have hinv : ‖lemma59LocalZeroFactor θ t z‖⁻¹ ≤
      (8 : ℝ) ^ lemma59LocalMultiplicity θ t := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (1 / 8 : ℝ) ^ lemma59LocalMultiplicity θ t) hp
    simpa [one_div_pow, one_div] using h
  rw [lemma59_actual_zero_removed_eq_quotient θ hθ hP, norm_div, div_eq_mul_inv]
  exact mul_le_mul
    (lemma59_actual_L_large_disk_bound θ hθ (sphere_subset_closedBall hz)) hinv
    (by positivity) (by positivity)

theorem lemma59_actual_zero_removed_closed_disk_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (15 / 8 : ℝ)) :
    ‖lemma59ZeroRemovedL θ t z‖ ≤
      8 * (r : ℝ) * (4 + |t|) * (8 : ℝ) ^ lemma59LocalMultiplicity θ t := by
  have hd : Differentiable ℂ (lemma59ZeroRemovedL θ t) := fun z =>
    (lemma59_actual_zero_removed_analytic θ hθ t z (mem_univ z)).differentiableAt
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball)
    hd.diffContOnCl
  · intro w hw
    rw [frontier_ball (lemma55JensenCenter t) (by norm_num : (15 / 8 : ℝ) ≠ 0)] at hw
    exact lemma59_actual_zero_removed_outer_bound θ hθ hw
  · rw [closure_ball (lemma55JensenCenter t) (by norm_num : (15 / 8 : ℝ) ≠ 0)]
    exact hz

theorem lemma59_actual_zero_removed_center_lower_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (1 : ℝ) / (4 * (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t) ≤
      ‖lemma59ZeroRemovedL θ t (lemma55JensenCenter t)‖ := by
  have hL := lemma56_actual_jensen_center_lower_bound θ t
  rw [lemma59_actual_zero_factorization θ hθ t (lemma55JensenCenter t), norm_mul] at hL
  have hP := lemma59_actual_zero_factor_center_bound θ hθ t
  have hprod := mul_le_mul_of_nonneg_right hP
    (norm_nonneg (lemma59ZeroRemovedL θ t (lemma55JensenCenter t)))
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hL, hprod]

noncomputable def lemma59JensenLogSize {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℝ :=
  Real.log (32 * (r : ℝ) * (4 + |t|))

noncomputable def lemma59ZeroRemovedRatioBound {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℝ :=
  32 * (r : ℝ) * (4 + |t|) * (14 : ℝ) ^ lemma59LocalMultiplicity θ t

lemma lemma59_jensen_log_size_pos {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : 0 < lemma59JensenLogSize θ t := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  apply Real.log_pos
  nlinarith only [hr1, abs_nonneg t]

theorem lemma59_zero_removed_ratio_bound_gt_one
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (t : ℝ) :
    1 < lemma59ZeroRemovedRatioBound θ t := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hpow : (1 : ℝ) ≤ 14 ^ lemma59LocalMultiplicity θ t := one_le_pow₀ (by norm_num)
  have hX : 1 < 32 * (r : ℝ) * (4 + |t|) := by nlinarith only [hr1, abs_nonneg t]
  unfold lemma59ZeroRemovedRatioBound
  nlinarith only [hX, hpow]

theorem lemma59_actual_zero_removed_ratio_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (15 / 8 : ℝ)) :
    ‖lemma59ZeroRemovedL θ t z /
      lemma59ZeroRemovedL θ t (lemma55JensenCenter t)‖ ≤
        lemma59ZeroRemovedRatioBound θ t := by
  have hc := lemma59_actual_zero_removed_center_lower_bound θ hθ t
  have hcp : 0 < ‖lemma59ZeroRemovedL θ t (lemma55JensenCenter t)‖ :=
    (by positivity : 0 < (1 : ℝ) / (4 * (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t)).trans_le hc
  have hinv : ‖lemma59ZeroRemovedL θ t (lemma55JensenCenter t)‖⁻¹ ≤
      4 * (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (1 : ℝ) / (4 * (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t)) hc
    simpa [one_div] using h
  rw [norm_div, div_eq_mul_inv]
  calc
    _ ≤ (8 * (r : ℝ) * (4 + |t|) * (8 : ℝ) ^ lemma59LocalMultiplicity θ t) *
        (4 * (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t) :=
      mul_le_mul (lemma59_actual_zero_removed_closed_disk_bound θ hθ hz) hinv
        (by positivity) (by positivity)
    _ = lemma59ZeroRemovedRatioBound θ t := by
      have he : (8 : ℝ) ^ lemma59LocalMultiplicity θ t *
          (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t = (14 : ℝ) ^ lemma59LocalMultiplicity θ t := by
        rw [← mul_pow]
        norm_num
      calc
        _ = (32 * (r : ℝ) * (4 + |t|)) * ((8 : ℝ) ^ lemma59LocalMultiplicity θ t *
          (7 / 4 : ℝ) ^ lemma59LocalMultiplicity θ t) := by ring
        _ = lemma59ZeroRemovedRatioBound θ t := by rw [he]; rfl

theorem lemma59_actual_zero_removed_log_ratio_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    Real.log (lemma59ZeroRemovedRatioBound θ t) ≤ 200 * lemma59JensenLogSize θ t := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hN := lemma59_actual_local_multiplicity_bound θ hθ t
  have h5 : Real.log (14 : ℝ) ≤ 13 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 14)]
  unfold lemma59ZeroRemovedRatioBound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hmul := mul_le_mul_of_nonneg_left h5
    (Nat.cast_nonneg (lemma59LocalMultiplicity θ t) : (0 : ℝ) ≤ _)
  change Real.log (32 * (r : ℝ) * (4 + |t|)) + _ ≤ _
  dsimp [lemma59JensenLogSize]
  have hlogpos := lemma59_jensen_log_size_pos θ t
  dsimp [lemma59JensenLogSize] at hlogpos
  nlinarith only [hN, hmul, hlogpos]

end ZhangLS.Spec
