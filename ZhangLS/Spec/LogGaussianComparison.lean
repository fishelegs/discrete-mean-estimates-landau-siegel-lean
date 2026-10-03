import ZhangLS.Spec.LogGaussianMellin
import ZhangLS.Spec.LogGaussianTail
import ZhangLS.Spec.FirstLogMoment
import ZhangLS.Spec.Lemma171GaussianComparison

/-! Correct-range arithmetic comparison for the logarithmic Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma171_log_smoothed_term_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (n : ℕ) : 0 ≤ lemma171LogSmoothedTerm χ n := by
  by_cases hn : n = 0
  · simp [hn, lemma171LogSmoothedTerm]
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact mul_nonneg (div_nonneg (lemma171_coefficient_nonneg χ n) hnp.le)
    (lemma171_log_gaussian_weight_nonneg hD (div_pos (lemma56_paper_T_pos D) hnp))

lemma lemma171_log_smoothed_term_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (n : ℕ) :
    lemma171LogSmoothedTerm χ n ≤
      (2 * lemma23PaperL D ^ 9) * (lemma171Coefficient χ n / (n : ℝ)) := by
  by_cases hn : n = 0
  · simp [hn, lemma171LogSmoothedTerm]
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hx : 0 < lemma171WeightArgument D n := div_pos (lemma56_paper_T_pos D) hnp
  have hT0 : 0 ≤ Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT, Real.log_exp]
    exact Real.rpow_nonneg (by linarith) _
  have hlog : Real.log (lemma171WeightArgument D n) ≤ Real.log (lemma56PaperT D) := by
    rw [lemma171WeightArgument, Real.log_div (lemma56_paper_T_pos D).ne' hnp.ne']
    linarith [Real.log_nonneg hn1]
  have hm : max (Real.log (lemma171WeightArgument D n)) 0 ≤ Real.log (lemma56PaperT D) :=
    max_le hlog hT0
  have hJ := lemma171_log_gaussian_weight_le hD hL hx
  have hT := lemma171_log_T_le hL
  have hp : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ hL
  unfold lemma171LogSmoothedTerm
  calc
    _ ≤ (lemma171Coefficient χ n / (n : ℝ)) * (2 * lemma23PaperL D ^ 9) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (div_nonneg (lemma171_coefficient_nonneg χ n) hnp.le)
    _ = _ := by ring

lemma lemma171_log_middle_smoothed_tail_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D ^ (-2013 : ℤ)) :
    (∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊, lemma171LogSmoothedTerm χ n) ≤
      2520 * lemma23PaperL D ^ (-2002 : ℤ) := by
  have htail : (∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊,
      lemma171Coefficient χ n / (n : ℝ)) ≤ 1260 * lemma23PaperL D ^ (-2011 : ℤ) := by
    simpa only [lemma171Coefficient, div_eq_mul_inv] using
      lemma31_actual_square_paper_tail_le χ hD hL hA hAbs
  have hL0 : 0 < lemma23PaperL D := by linarith
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊,
        (2 * lemma23PaperL D ^ 9) * (lemma171Coefficient χ n / (n : ℝ)) :=
      Finset.sum_le_sum (fun n _ => lemma171_log_smoothed_term_le χ hD hL n)
    _ = (2 * lemma23PaperL D ^ 9) *
        ∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊,
          lemma171Coefficient χ n / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (2 * lemma23PaperL D ^ 9) * (1260 * lemma23PaperL D ^ (-2011 : ℤ)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 2520 * (lemma23PaperL D ^ (9 : ℤ) * lemma23PaperL D ^ (-2011 : ℤ)) := by
      rw [zpow_ofNat]
      ring
    _ = _ := by rw [← zpow_add₀ hL0.ne']; norm_num

lemma lemma171_log_strict_cutoff_endpoint {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (∑ n ∈ Finset.Icc 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ) *
      Real.log (lemma56PaperT D / n)) =
      Real.log (lemma56PaperT D) * lemma171ShortHarmonicSum χ - lemma171FirstLogMoment χ +
        (Real.log (lemma56PaperT D) - 4 * lemma23PaperL D) * (D : ℝ) ^ (-4 : ℤ) := by
  have hD : 1 ≤ D ^ 4 := Nat.one_le_pow 4 D χ.modulus_pos
  have h := Finset.sum_Ico_add_eq_sum_Icc
    (f := fun n : ℕ => lemma171Coefficient χ n / (n : ℝ) * Real.log (lemma56PaperT D / n)) hD
  dsimp only at h
  have hshort : (∑ n ∈ Finset.Ico 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ) *
      Real.log (lemma56PaperT D / n)) =
      Real.log (lemma56PaperT D) * lemma171ShortHarmonicSum χ - lemma171FirstLogMoment χ := by
    rw [← lemma171_log_weighted_short_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mp (Finset.mem_Ico.mp hn).1
    rw [Real.log_div (lemma56_paper_T_pos D).ne' hn0]
  rw [hshort, lemma171_coefficient_modulus_power, Nat.cast_pow,
    Real.log_div (lemma56_paper_T_pos D).ne' (pow_ne_zero 4 (Nat.cast_ne_zero.mpr χ.modulus_ne_zero)),
    Real.log_pow] at h
  simpa [lemma23PaperL, zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_comm] using h.symm

end ZhangLS.Spec
