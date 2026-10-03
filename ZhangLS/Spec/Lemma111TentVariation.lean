import ZhangLS.Spec.Lemma111PrimitiveVariation

/-! Uniform discrete variation of both literal Gaussian tent errors. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped BigOperators

noncomputable def lemma111SequenceVariation (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  |f N| + ∑ n ∈ range N, |f (n+1) - f n|

lemma lemma111_sequence_variation_neg (f : ℕ → ℝ) (N : ℕ) :
    lemma111SequenceVariation (fun n => -f n) N = lemma111SequenceVariation f N := by
  unfold lemma111SequenceVariation
  rw [abs_neg]
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [neg_sub_neg, abs_sub_comm]

lemma lemma111_sequence_variation_add (f g : ℕ → ℝ) (N : ℕ) :
    lemma111SequenceVariation (fun n => f n + g n) N ≤
      lemma111SequenceVariation f N + lemma111SequenceVariation g N := by
  unfold lemma111SequenceVariation
  calc
    _ ≤ (|f N| + |g N|) + ∑ n ∈ range N,
        (|f (n+1) - f n| + |g (n+1) - g n|) := by
      apply add_le_add (abs_add_le _ _) (sum_le_sum _)
      intro n hn
      convert abs_add_le (f (n+1) - f n) (g (n+1) - g n) using 1 <;> congr 1 <;> ring
    _ = _ := by rw [sum_add_distrib]; ring

lemma lemma111_sequence_variation_mul (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    lemma111SequenceVariation (fun n => c * f n) N =
      |c| * lemma111SequenceVariation f N := by
  simp only [lemma111SequenceVariation, ← mul_sub, abs_mul, ← mul_sum, mul_add]

noncomputable def lemma111TentErrorProfile (D : ℕ) (a b c u : ℝ) : ℝ :=
  500 * (lemma111PrimitiveError D (c-u) -
    2 * lemma111PrimitiveError D (b-u) + lemma111PrimitiveError D (a-u))

lemma lemma111_tent_error_profile_variation {D : ℕ} (hD : 1 < D)
    (a b c : ℝ) (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ) :
    lemma111SequenceVariation (fun n => lemma111TentErrorProfile D a b c (u n)) N ≤
      16000 / lemma111Scale D := by
  have hv (k : ℝ) : lemma111SequenceVariation
      (fun n => lemma111PrimitiveError D (k-u n)) N ≤ 8 / lemma111Scale D := by
    exact lemma111_primitive_error_variation hD _ (fun i j hij => sub_le_sub_left (hu hij) k) N
  let fa := fun n => lemma111PrimitiveError D (a-u n)
  let fb := fun n => lemma111PrimitiveError D (b-u n)
  let fc := fun n => lemma111PrimitiveError D (c-u n)
  have hab := lemma111_sequence_variation_add fc (fun n => -2 * fb n) N
  have habc := lemma111_sequence_variation_add (fun n => fc n + -2 * fb n) fa N
  rw [lemma111_sequence_variation_mul] at hab
  norm_num at hab
  have heq : (fun n => lemma111TentErrorProfile D a b c (u n)) =
      fun n => 500 * ((fc n + -2 * fb n) + fa n) := by
    funext n
    dsimp [lemma111TentErrorProfile, fa, fb, fc]
    ring
  rw [heq, lemma111_sequence_variation_mul]
  norm_num
  have hva := hv a
  have hvb := hv b
  have hvc := hv c
  change lemma111SequenceVariation fa N ≤ _ at hva
  change lemma111SequenceVariation fb N ≤ _ at hvb
  change lemma111SequenceVariation fc N ≤ _ at hvc
  simp only [div_eq_mul_inv] at hva hvb hvc ⊢
  simp only [neg_mul] at habc
  linarith

noncomputable def lemma111TentErrorOne (D : ℕ) (y : ℝ) : ℝ :=
  lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) - lemma111SmoothedOne D y

lemma lemma111_tent_error_one_eq {D : ℕ} (hD : 1 < D) {y : ℝ} (hy : 0 < y) :
    lemma111TentErrorOne D y =
      -lemma111TentErrorProfile D (1/2) (251/500) (63/125)
        (Real.log y / Real.log (lemma23PaperP D)) := by
  rw [lemma111TentErrorOne, lemma111_tent_second_difference,
    lemma111_smoothed_second_difference hD hy]
  dsimp [lemma111TentErrorProfile, lemma111PrimitiveError]
  ring

lemma lemma111_log_coordinate_monotone {D : ℕ} (hD : 1 < D)
    (y : ℕ → ℝ) (hy : ∀ n, 0 < y n) (hm : Monotone y) :
    Monotone (fun n => Real.log (y n) / Real.log (lemma23PaperP D)) := by
  intro i j hij
  apply div_le_div_of_nonneg_right (Real.log_le_log (hy i) (hm hij))
  simp only [lemma23PaperP, Real.log_exp]
  exact pow_nonneg (Real.log_natCast_nonneg D) _

/-- Last-endpoint convention, directly usable in finite Abel summation.
The sample can be `d*r*(n+1)` or any increasing positive sequence. -/
lemma lemma111_tent_error_one_variation {D : ℕ} (hD : 1 < D)
    (y : ℕ → ℝ) (hy : ∀ n, 0 < y n) (hm : Monotone y) (N : ℕ) :
    lemma111SequenceVariation (fun n => lemma111TentErrorOne D (y n)) N ≤
      16000 / lemma111Scale D := by
  have he : (fun n => lemma111TentErrorOne D (y n)) =
      fun n => -lemma111TentErrorProfile D (1/2) (251/500) (63/125)
        (Real.log (y n) / Real.log (lemma23PaperP D)) := by
    funext n
    exact lemma111_tent_error_one_eq hD (hy n)
  rw [he, lemma111_sequence_variation_neg]
  exact lemma111_tent_error_profile_variation hD _ _ _ _
    (lemma111_log_coordinate_monotone hD y hy hm) N

noncomputable def lemma111ShiftScale (D : ℕ) : ℝ := (D : ℝ) * lemma23PaperL D ^ 519

lemma lemma111_shift_scale_pos {D : ℕ} (hD : 1 < D) :
    0 < lemma111ShiftScale D := by
  unfold lemma111ShiftScale
  exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hD))
    (pow_pos (Real.log_pos (by exact_mod_cast hD)) _)

noncomputable def lemma111TentErrorTwo (D : ℕ) (y : ℝ) : ℝ :=
  lemma111Tent (Real.log (y / lemma111ShiftScale D) / Real.log (lemma23PaperP D) + 1/250) -
    lemma111SmoothedTwo D y

lemma lemma111_smoothed_two_second_difference {D : ℕ} (hD : 1 < D)
    {y : ℝ} (hy : 0 < y) :
    lemma111SmoothedTwo D y =
      let u := Real.log (y / lemma111ShiftScale D) / Real.log (lemma23PaperP D)
      500 * (lemma111Primitive D (1/2-u) -
        2 * lemma111Primitive D (249/500-u) + lemma111Primitive D (62/125-u)) := by
  have hq := lemma111_shift_scale_pos hD
  have he (z : ℝ) : lemma23PaperP D ^ z * (D:ℝ) * lemma23PaperL D ^ 519 / y =
      lemma23PaperP D ^ z / (y / lemma111ShiftScale D) := by
    rw [div_div_eq_mul_div]
    dsimp [lemma111ShiftScale]
    ring
  unfold lemma111SmoothedTwo
  simp_rw [he, lemma111_weight_log_coordinate hD (div_pos hy hq)]
  rw [lemma111_integral_profile hD, lemma111_integral_profile hD]
  ring

lemma lemma111_tent_error_two_eq {D : ℕ} (hD : 1 < D) {y : ℝ} (hy : 0 < y) :
    lemma111TentErrorTwo D y =
      -lemma111TentErrorProfile D (62/125) (249/500) (1/2)
        (Real.log (y / lemma111ShiftScale D) / Real.log (lemma23PaperP D)) := by
  rw [lemma111TentErrorTwo, lemma111_tent_second_difference,
    lemma111_smoothed_two_second_difference hD hy]
  dsimp [lemma111TentErrorProfile, lemma111PrimitiveError]
  have ha (u : ℝ) : (1/2 : ℝ) - (u + 1/250) = 62/125-u := by ring
  have hb (u : ℝ) : (251/500 : ℝ) - (u + 1/250) = 249/500-u := by ring
  have hc (u : ℝ) : (63/125 : ℝ) - (u + 1/250) = 1/2-u := by ring
  rw [ha, hb, hc]
  ring

lemma lemma111_tent_error_two_variation {D : ℕ} (hD : 1 < D)
    (y : ℕ → ℝ) (hy : ∀ n, 0 < y n) (hm : Monotone y) (N : ℕ) :
    lemma111SequenceVariation (fun n => lemma111TentErrorTwo D (y n)) N ≤
      16000 / lemma111Scale D := by
  have he : (fun n => lemma111TentErrorTwo D (y n)) =
      fun n => -lemma111TentErrorProfile D (62/125) (249/500) (1/2)
        (Real.log (y n / lemma111ShiftScale D) / Real.log (lemma23PaperP D)) := by
    funext n
    exact lemma111_tent_error_two_eq hD (hy n)
  rw [he, lemma111_sequence_variation_neg]
  apply lemma111_tent_error_profile_variation hD
  apply lemma111_log_coordinate_monotone hD
  · exact fun n => div_pos (hy n) (lemma111_shift_scale_pos hD)
  · exact fun i j hij => div_le_div_of_nonneg_right (hm hij) (lemma111_shift_scale_pos hD).le

lemma lemma111_tent_error_two_original_coordinate {D : ℕ} (hD : 1 < D)
    {y : ℝ} (hy : 0 < y) :
    lemma111TentErrorTwo D y =
      lemma111Tent (Real.log y / Real.log (lemma23PaperP D) + 1/250 -
        Real.log ((D:ℝ) * lemma23PaperL D ^ 519) / Real.log (lemma23PaperP D)) -
      lemma111SmoothedTwo D y := by
  unfold lemma111TentErrorTwo
  rw [Real.log_div hy.ne' (lemma111_shift_scale_pos hD).ne']
  congr 2
  dsimp [lemma111ShiftScale]
  ring

lemma lemma111_div_scale_eq_log_zpow (D : ℕ) (C : ℝ) :
    C / lemma111Scale D = C * lemma23PaperL D ^ (-24 : ℤ) := by
  change C * (lemma23PaperL D ^ (24 : ℕ))⁻¹ = C * lemma23PaperL D ^ (-24 : ℤ)
  rw [zpow_neg, zpow_ofNat]

@[simp] lemma lemma111_smoothed_one_zero (D : ℕ) : lemma111SmoothedOne D 0 = 0 := by
  norm_num [lemma111SmoothedOne, intervalIntegral.integral_const] <;> ring

@[simp] lemma lemma111_smoothed_two_zero (D : ℕ) : lemma111SmoothedTwo D 0 = 0 := by
  norm_num [lemma111SmoothedTwo, intervalIntegral.integral_const] <;> ring

@[simp] lemma lemma111_tent_error_one_zero (D : ℕ) : lemma111TentErrorOne D 0 = 0 := by
  norm_num [lemma111TentErrorOne, lemma111Tent]

@[simp] lemma lemma111_tent_error_two_zero (D : ℕ) : lemma111TentErrorTwo D 0 = 0 := by
  norm_num [lemma111TentErrorTwo, lemma111Tent]

end ZhangLS.Spec
