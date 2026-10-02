import ZhangLS.Spec.Lemma56ZeroPowerDerivatives

/-! # Uniform weighted actual power-sum errors for every degree

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

open Finset

noncomputable def lemma56WeightedZeroPowerSum {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (t r : ℝ) (v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    lemma56LocalZeroPowerSum θ t (2 * (j + 1)) / (r : ℂ) ^ (j + 1)

noncomputable def lemma56WeightedLogDerivative {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (t r : ℝ) (v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    lemma56NormalizedDerivative θ t (2 * j + 1) / (r : ℂ) ^ (j + 1)

theorem lemma56_actual_normalized_odd_power_error_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {L : ℝ} (hL : 2000 ≤ L) {t : ℝ}
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r) (j : ℕ) :
    ‖(lemma56NormalizedDerivative θ t (2 * j + 1) -
      lemma56LocalZeroPowerSum θ t (2 * (j + 1))) / (r : ℂ) ^ (j + 1)‖ ≤
        (720 * lemma56JensenLogSize θ t) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j) := by
  have hLp : 0 < lemma56JensenLogSize θ t := lemma56_jensen_log_size_pos θ t
  have hb := lemma56_actual_power_sum_remainder_bound θ hθ (t := t) (2 * j + 1)
  have hn : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [hn] at hb
  have hq := lemma55_normalized_remainder_geometric_ratio hL hr hlower
  rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hr,
    div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ (450 * (((2 * j + 1 : ℕ) : ℝ) + 1) * lemma56JensenLogSize θ t *
        (8 / 9 : ℝ) ^ (2 * (j + 1))) * r⁻¹ ^ (j + 1) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (900 * ((j : ℝ) + 1) * lemma56JensenLogSize θ t) *
        ((64 / 81 : ℝ) * r⁻¹) ^ (j + 1) := by
      rw [pow_mul, mul_pow]
      push_cast
      norm_num only [show (8 / 9 : ℝ) ^ 2 = 64 / 81 by norm_num]
      ring
    _ ≤ (900 * ((j : ℝ) + 1) * lemma56JensenLogSize θ t) * (4 / 5 : ℝ) ^ (j + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq (j + 1)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem lemma56_actual_weighted_power_error_uniform_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {L : ℝ} (hL : 2000 ≤ L) {t : ℝ}
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma56WeightedLogDerivative θ t r v J - lemma56WeightedZeroPowerSum θ t r v J‖ ≤
      36000 * lemma56JensenLogSize θ t := by
  have hLp : 0 < lemma56JensenLogSize θ t := lemma56_jensen_log_size_pos θ t
  unfold lemma56WeightedLogDerivative lemma56WeightedZeroPowerSum
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range J,
        ‖(lemma55FejerDetectionWeight v J j : ℂ) * lemma56NormalizedDerivative θ t (2 * j + 1) /
            (r : ℂ) ^ (j + 1) -
          (lemma55FejerDetectionWeight v J j : ℂ) * lemma56LocalZeroPowerSum θ t (2 * (j + 1)) /
            (r : ℂ) ^ (j + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range J, (1440 * lemma56JensenLogSize θ t) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j) := by
      apply sum_le_sum
      intro j _
      have hw := lemma55_fejer_detection_weight_bounds hv J j
      have he : (lemma55FejerDetectionWeight v J j : ℂ) * lemma56NormalizedDerivative θ t (2 * j + 1) /
          (r : ℂ) ^ (j + 1) -
        (lemma55FejerDetectionWeight v J j : ℂ) * lemma56LocalZeroPowerSum θ t (2 * (j + 1)) /
          (r : ℂ) ^ (j + 1) =
        (lemma55FejerDetectionWeight v J j : ℂ) *
          ((lemma56NormalizedDerivative θ t (2 * j + 1) -
            lemma56LocalZeroPowerSum θ t (2 * (j + 1))) / (r : ℂ) ^ (j + 1)) := by ring
      rw [he, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1]
      have hb := lemma56_actual_normalized_odd_power_error_bound θ hθ hL (t := t) hr hlower j
      calc
        _ ≤ 2 * ((720 * lemma56JensenLogSize θ t) * (((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j)) :=
          mul_le_mul hw.2 hb (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    _ = (1440 * lemma56JensenLogSize θ t) * ∑ j ∈ range J, ((j : ℝ) + 1) * (4 / 5 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ (1440 * lemma56JensenLogSize θ t) * 25 := mul_le_mul_of_nonneg_left
      (lemma55_successor_geometric_finite_bound (range J)) (by positivity)
    _ = _ := by ring

theorem lemma56_actual_weighted_real_power_error_uniform_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {L : ℝ} (hL : 2000 ≤ L) {t : ℝ}
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    |(lemma56WeightedLogDerivative θ t r v J).re -
      (lemma56WeightedZeroPowerSum θ t r v J).re| ≤ 36000 * lemma56JensenLogSize θ t := by
  have h := abs_re_le_norm (lemma56WeightedLogDerivative θ t r v J -
    lemma56WeightedZeroPowerSum θ t r v J)
  rw [sub_re] at h
  exact h.trans (lemma56_actual_weighted_power_error_uniform_bound θ hθ hL hr hlower hv J)

end ZhangLS.Spec
