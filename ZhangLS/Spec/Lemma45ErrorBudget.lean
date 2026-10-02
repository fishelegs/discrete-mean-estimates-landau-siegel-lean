import ZhangLS.Spec.Lemma45Normalization
import ZhangLS.Spec.RiemannZetaCriticalLineBound

/-! # Explicit absolute constants for the zero-free estimate -/

namespace ZhangLS.Spec

open Complex
open scoped ComplexOrder

set_option maxHeartbeats 1000000

theorem lemma45_divisor_series_mass_le : lemma44DivisorSeriesMass ≤ 36 := by
  have hnonneg (n : ℕ) : 0 ≤ lemma44DivisorCoefficient n := by
    simp only [lemma44DivisorCoefficient, LSeries.convolution_def]
    exact Finset.sum_nonneg (fun _ _ => by norm_num)
  have ht (n : ℕ) : LSeries.term lemma44DivisorCoefficient (5 / 4 : ℂ) n =
      (‖LSeries.term lemma44DivisorCoefficient (5 / 4 : ℂ) n‖ : ℂ) := by
    have h := LSeries.term_nonneg (hnonneg n) (5 / 4)
    have ha : ((5 / 4 : ℝ) : ℂ) = (5 / 4 : ℂ) := by push_cast; rfl
    rw [ha] at h
    exact Complex.eq_coe_norm_of_nonneg h
  have hm : (lemma44DivisorSeriesMass : ℂ) =
      LSeries lemma44DivisorCoefficient (5 / 4 : ℂ) := by
    simp only [lemma44DivisorSeriesMass, Complex.ofReal_tsum, LSeries,
      ← ht]
  have hs : LSeriesSummable (1 : ℕ → ℂ) (5 / 4 : ℂ) :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  rw [lemma44DivisorCoefficient, LSeries_convolution' hs hs,
    LSeries_one_eq_riemannZeta (by norm_num)] at hm
  have hb := norm_riemannZeta_le_fractionalPart_formula
    (s := (5 / 4 : ℂ)) (by norm_num) (by norm_num)
  have hnorm : ‖riemannZeta (5 / 4 : ℂ)‖ ≤ 6 := by
    norm_num [show (5 / 4 : ℂ) = ((5 / 4 : ℝ) : ℂ) by push_cast; rfl,
      show (5 / 4 : ℂ) - 1 = ((1 / 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at hb
    linarith only [hb]
  have h := congrArg norm hm
  rw [Complex.norm_of_nonneg lemma44_divisor_series_mass_nonneg, norm_mul] at h
  nlinarith [norm_nonneg (riemannZeta (5 / 4 : ℂ))]

theorem lemma45_inverse_square_mass_le : lemma44InverseSquareMass ≤ 3 := by
  have hm : (lemma44InverseSquareMass : ℂ) = riemannZeta (2 : ℂ) := by
    have hz := zeta_nat_eq_tsum_of_gt_one (k := 2) (by norm_num)
    norm_num only [Nat.cast_ofNat] at hz
    rw [hz]
    simp [lemma44InverseSquareMass, Complex.ofReal_tsum, one_div]
  have hb := norm_riemannZeta_le_fractionalPart_formula
    (s := (2 : ℂ)) (by norm_num) (by norm_num)
  norm_num at hb
  have h := congrArg norm hm
  have hn : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  rw [Complex.norm_of_nonneg hn] at h
  exact h.le.trans hb

/-- A deliberately generous, closed bound for the absolute Mellin error. -/
theorem lemma45_error_constant_le : lemma44ErrorConstant ≤ (3 : ℝ) ^ 60 := by
  have hd := lemma45_divisor_series_mass_le
  have hi := lemma45_inverse_square_mass_le
  have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have he (x : ℝ) (hx : x ≤ 19) : Real.exp x ≤ (3 : ℝ) ^ 19 := by
    calc
      Real.exp x ≤ Real.exp (19 * 1) := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp 1) ^ 19 := Real.exp_nat_mul 1 19
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le he1 19
  have h2 := he (2 * Real.pi) (by linarith [Real.pi_le_four])
  have h3 := he (1 + (9 / 5 : ℝ) * Real.pi) (by linarith [Real.pi_le_four])
  have h4 := he (3 + 4 * Real.pi) (by linarith [Real.pi_le_four])
  have hdn := lemma44_divisor_series_mass_nonneg
  unfold lemma44ErrorConstant lemma44ErrorConstant180
  have hmul1 := mul_le_mul hd he1 (Real.exp_pos 1).le (by norm_num : (0 : ℝ) ≤ 36)
  have hmul2 := mul_le_mul hd h3 (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 36)
  norm_num at hmul1 hmul2 h2 h4 ⊢
  nlinarith only [hd, hi, he1, h2, h4, hmul1, hmul2]

theorem lemma45_normalized_error_budget {L : ℝ} (hL : 3 ≤ L) :
    (4 * lemma44ErrorConstant) * L ^ (-100 : ℤ) ≤ (L ^ 9)⁻¹ / 4 := by
  have hpos : 0 < L := by linarith
  have hc : 16 * lemma44ErrorConstant ≤ L ^ 91 := by
    have hp : (3 : ℝ) ^ 91 ≤ L ^ 91 := pow_le_pow_left₀ (by norm_num) hL 91
    have hb := lemma45_error_constant_le
    have hn : 16 * (3 : ℝ) ^ 60 ≤ (3 : ℝ) ^ 91 := by norm_num
    linarith
  rw [zpow_neg, zpow_ofNat]
  have hpow : L ^ 100 = L ^ 91 * L ^ 9 := by rw [← pow_add]
  rw [hpow, mul_inv]
  have hb : (4 * lemma44ErrorConstant) * (L ^ 91)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div, mul_one_div]
    apply (div_le_iff₀ (pow_pos hpos 91)).mpr
    linarith
  calc
    _ = ((4 * lemma44ErrorConstant) * (L ^ 91)⁻¹) * (L ^ 9)⁻¹ := by ring
    _ ≤ (1 / 4) * (L ^ 9)⁻¹ := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

end ZhangLS.Spec
