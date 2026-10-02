import ZhangLS.Spec.Lemma51Parameters
import ZhangLS.Spec.Lemma23ZeroData

/-! # The three original shifts and the L⁻¹²³ error scale -/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

theorem lemma52_offset_sum (D : ℕ) (c : ℝ) :
    lemma23PaperOffsetOne D c + lemma23PaperOffsetTwo D c + lemma23PaperOffsetThree D c =
      2 * lemma23PaperOffsetThree D c := by
  unfold lemma23PaperOffsetOne lemma23PaperOffsetTwo lemma23PaperOffsetThree
  ring

theorem lemma52_offset_bounds {D : ℕ} {c : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 10) :
    (0 ≤ lemma23PaperOffsetOne D c ∧ lemma23PaperOffsetOne D c ≤ 3 * lemma44PaperAlpha D) ∧
    (0 ≤ lemma23PaperOffsetTwo D c ∧ lemma23PaperOffsetTwo D c ≤ 3 * lemma44PaperAlpha D) ∧
    (0 ≤ lemma23PaperOffsetThree D c ∧ lemma23PaperOffsetThree D c ≤ 3 * lemma44PaperAlpha D) := by
  let a := lemma44PaperAlpha D
  let u := c * a * lemma23PaperL D
  have ha : 0 < a := (lemma44_alpha_pos_le_one hL).1
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hus : u ≤ 1 / 10 := hsmall
  have h1 : lemma23PaperOffsetOne D c = a * (1 - 5 * u) := by
    dsimp [lemma23PaperOffsetOne, a, u]
    ring
  have h2 : lemma23PaperOffsetTwo D c = 2 * a * (1 + u) := by
    dsimp [lemma23PaperOffsetTwo, a, u]
  have h3 : lemma23PaperOffsetThree D c = 3 * a * (1 - u) := by
    dsimp [lemma23PaperOffsetThree, a, u]
  rw [h1, h2, h3]
  change (0 ≤ a * (1 - 5 * u) ∧ a * (1 - 5 * u) ≤ 3 * a) ∧
    (0 ≤ 2 * a * (1 + u) ∧ 2 * a * (1 + u) ≤ 3 * a) ∧
    (0 ≤ 3 * a * (1 - u) ∧ 3 * a * (1 - u) ≤ 3 * a)
  have hau : 0 ≤ a * u := mul_nonneg ha.le hu
  have has : a * u ≤ a / 10 := by nlinarith [mul_le_mul_of_nonneg_left hus ha.le]
  constructor
  · constructor <;> nlinarith
  constructor <;> constructor <;> nlinarith

theorem lemma52_offset_shift_window {D : ℕ} {b : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hb : 0 ≤ b) (hbhi : b ≤ 3 * lemma44PaperAlpha D) :
    (I * (b : ℂ)).re = 0 ∧ |(I * (b : ℂ)).im| < lemma23PaperL D ^ 20 := by
  have ha := lemma51_alpha_le_quarter hL
  have hpow : 1 ≤ lemma23PaperL D ^ 20 := one_le_pow₀ (by linarith)
  simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im, zero_mul, mul_zero,
    sub_zero, mul_im, one_mul, zero_add, abs_of_nonneg hb]
  exact ⟨trivial, by linarith⟩

theorem lemma52_alpha_error_scale {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    lemma44PaperAlpha D * lemma23PaperL D ^ (-114 : ℤ) =
      Real.pi * lemma23PaperL D ^ (-123 : ℤ) := by
  have hne : lemma23PaperL D ≠ 0 := by linarith
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp, div_eq_mul_inv, mul_assoc, ← zpow_natCast (lemma23PaperL D) 9,
    ← zpow_neg, ← zpow_add₀ hne]
  norm_num

theorem lemma52_log_error_small {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    63 * Real.pi * lemma23PaperL D ^ (-123 : ℤ) ≤ 1 := by
  have hpos : 0 < lemma23PaperL D := by linarith
  have hpow : (3 : ℝ) ^ 7 ≤ lemma23PaperL D ^ 123 :=
    (pow_le_pow_left₀ (by norm_num) hL 7).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
  change 63 * Real.pi * (lemma23PaperL D ^ (123 : ℕ))⁻¹ ≤ 1
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos hpos 123)).mpr
  norm_num at hpow
  nlinarith [Real.pi_le_four]

theorem lemma52_exists_shift_threshold {c : ℝ} (hc : 0 < c) :
    ∃ D₀ : ℕ, lemma23SectionFourModulusThreshold ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 10 := by
  obtain ⟨D₀, hD₀, hsmall⟩ := lemma46_exists_contraction_threshold
    (c := 5 * c) (by positivity)
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  nlinarith only [hsmall D hD]

end ZhangLS.Spec
