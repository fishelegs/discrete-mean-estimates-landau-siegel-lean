import ZhangLS.Spec.Lemma55ZetaWeightedPowerError

/-! # Actual exceptional-zero tails outside a local disk

Distance at least 5/4 gives a geometric weighted tail at most four, uniformly in every detection degree and candidate normalization.
-/

namespace ZhangLS.Spec
open Complex Finset Metric Set

lemma lemma55_distant_inverse_square_ratio {L r : ℝ} (hL : 2000 ≤ L)
    (hr : 0 < r) (hlower : ((1 + 2 / L)⁻¹) ^ 2 ≤ r) {z : ℂ}
    (hz : (5 / 4 : ℝ) ≤ ‖z‖) : ‖z⁻¹ ^ 2 / (r : ℂ)‖ ≤ 2 / 3 := by
  have hzp : 0 < ‖z‖ := by linarith only [hz]
  have hi : ‖z‖⁻¹ ≤ 4 / 5 := by
    simpa using (inv_le_inv₀ hzp (by norm_num : (0 : ℝ) < 5 / 4)).mpr hz
  have hp : (‖z‖⁻¹) ^ 2 ≤ (16 / 25 : ℝ) := by
    simpa only [show (4 / 5 : ℝ) ^ 2 = 16 / 25 by norm_num] using
      pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg z)) hi 2
  have hq := lemma55_normalized_remainder_geometric_ratio hL hr hlower
  rw [norm_div, norm_pow, norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_eq_mul_inv]
  calc
    _ ≤ (16 / 25 : ℝ) * r⁻¹ := mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hr.le)
    _ = (81 / 100 : ℝ) * ((64 / 81 : ℝ) * r⁻¹) := by ring
    _ ≤ (81 / 100 : ℝ) * (4 / 5) := mul_le_mul_of_nonneg_left hq (by norm_num)
    _ ≤ _ := by norm_num

lemma lemma55_distant_geometric_sum_bound (S : Finset ℕ) :
    (∑ j ∈ S, (2 / 3 : ℝ) ^ (j + 1)) ≤ 2 := by
  have hs : HasSum (fun j : ℕ => (2 / 3 : ℝ) ^ (j + 1)) (2 : ℝ) := by
    convert (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)).mul_left (2 / 3 : ℝ) using 1
    · ext j
      rw [pow_succ]
      ring
    · norm_num
  calc
    _ ≤ ∑' j : ℕ, (2 / 3 : ℝ) ^ (j + 1) := hs.summable.sum_le_tsum S (fun _ _ => by positivity)
    _ = _ := hs.tsum_eq

lemma lemma55_distant_weighted_kernel_bound {u v : ℂ} (hu : ‖u‖ ≤ 2 / 3)
    (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) * u ^ (j + 1)‖ ≤ 4 := by
  calc
    _ ≤ ∑ j ∈ range J, ‖(lemma55FejerDetectionWeight v J j : ℂ) * u ^ (j + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range J, 2 * (2 / 3 : ℝ) ^ (j + 1) := by
      apply sum_le_sum
      intro j _
      have hw := lemma55_fejer_detection_weight_bounds hv J j
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1, norm_pow]
      exact mul_le_mul hw.2 (pow_le_pow_left₀ (norm_nonneg u) hu (j + 1)) (by positivity) (by norm_num)
    _ = 2 * ∑ j ∈ range J, (2 / 3 : ℝ) ^ (j + 1) := by rw [mul_sum]
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (lemma55_distant_geometric_sum_bound (range J)) (by norm_num)
    _ = _ := by norm_num

noncomputable def lemma55WeightedExceptionalTail (t β r : ℝ) (v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    (lemma55JensenCenter t - (β : ℂ))⁻¹ ^ (2 * (j + 1)) / (r : ℂ) ^ (j + 1)

lemma lemma55_actual_exceptional_outside_local_disk_distance {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) {β : ℝ}
    (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hout : (β : ℂ) ∉ lemma55LocalZeroFinset χ t) :
    (5 / 4 : ℝ) ≤ ‖lemma55JensenCenter t - (β : ℂ)‖ := by
  have hb : (β : ℂ) ∉ closedBall (lemma55JensenCenter t) (5 / 4 : ℝ) := by
    intro hb
    exact hout ((lemma55_mem_actual_local_zero_finset χ hD t (β : ℂ)).mpr ⟨hb, hzero⟩)
  rw [mem_closedBall_iff_norm, norm_sub_rev] at hb
  exact (lt_of_not_ge hb).le

lemma lemma55_actual_exceptional_outside_local_disk_tail_bound {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    (t : ℝ) {β r : ℝ} (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hout : (β : ℂ) ∉ lemma55LocalZeroFinset χ t) (hr : 0 < r)
    (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedExceptionalTail t β r v J‖ ≤ 4 := by
  have hu := lemma55_distant_inverse_square_ratio hL hr hlower
    (lemma55_actual_exceptional_outside_local_disk_distance χ hD t hzero hout)
  have heq : lemma55WeightedExceptionalTail t β r v J =
      ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (((lemma55JensenCenter t - (β : ℂ))⁻¹ ^ 2) / (r : ℂ)) ^ (j + 1) := by
    unfold lemma55WeightedExceptionalTail
    apply sum_congr rfl
    intro j _
    rw [div_pow, pow_mul]
    ring
  rw [heq]
  exact lemma55_distant_weighted_kernel_bound hu hv J

end ZhangLS.Spec
