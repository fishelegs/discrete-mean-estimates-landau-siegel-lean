import ZhangLS.Spec.Lemma171GaussianMellin
import ZhangLS.Spec.Lemma44SmoothedTail

/-!
# Lemma 17.1: arithmetic comparison for Gaussian unsmoothing

The middle interval is the completed Lemma 3.1 tail with the Gaussian weight
bounded between zero and one. The exact strict D⁴ endpoint is retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma171_smoothed_term_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (n : ℕ) : 0 ≤ lemma171SmoothedTerm χ n := by
  by_cases hn : n = 0
  · simp [hn,lemma171SmoothedTerm]
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact mul_nonneg (div_nonneg (lemma171_coefficient_nonneg χ n) hnp.le)
    (zhangGaussianWeight_nonneg hD (div_pos (lemma56_paper_T_pos D) hnp))

lemma lemma171_smoothed_term_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (n : ℕ) :
    lemma171SmoothedTerm χ n ≤ lemma171Coefficient χ n / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn,lemma171SmoothedTerm]
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hx : 0 < lemma171WeightArgument D n := div_pos (lemma56_paper_T_pos D) hnp
  have ht := zhangGaussianWeight_nonneg hD (inv_pos.mpr hx)
  rw [lemma44_gaussian_weight_inv] at ht
  unfold lemma171SmoothedTerm
  exact mul_le_of_le_one_right (div_nonneg (lemma171_coefficient_nonneg χ n) hnp.le)
    (by linarith)

lemma lemma171_middle_smoothed_tail_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ)) :
    (∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊, lemma171SmoothedTerm χ n) ≤
      1260*lemma23PaperL D^(-2011 : ℤ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
      lemma171Coefficient χ n/(n : ℝ) := by
        exact Finset.sum_le_sum (fun n _ => lemma171_smoothed_term_le χ hD n)
    _ ≤ _ := by
      simpa only [lemma171Coefficient,div_eq_mul_inv] using
        lemma31_actual_square_paper_tail_le χ hD hL hA hAbs

end ZhangLS.Spec
