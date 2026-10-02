import ZhangLS.Spec.Lemma56PrimeWeightIdentity

/-! # Actual finite Abel conversion for original Lemma 5.6

Actual prime-mass normalization and the faithful principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_paper_prime_weight_parameters {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    1 ≤ Real.log (lemma23PaperP D) ∧ 4 ≤ lemma23PaperP D ∧
      lemma23PaperP D ≤ lemma56PrimeUpper D ∧
      lemma56PrimeUpper D + 1 ≤ 2 * lemma23PaperP D ∧
      (⌈lemma56PrimeUpper D⌉₊ : ℝ) ≤ 2 * lemma23PaperP D := by
  let L := lemma23PaperL D
  have hL0 : 0 ≤ L := by dsimp [L]; linarith only [hL]
  have hL2 : (2 : ℝ) ≤ L := by dsimp [L]; linarith only [hL]
  have h512 : 512 ≤ L ^ 9 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL2 9
    norm_num at hh
    exact hh
  have hL68 : 4 ≤ L ^ 68 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL2 68
    norm_num at hh
    linarith only [hh]
  have hδ0 : 0 ≤ L ^ (-68 : ℤ) := zpow_nonneg hL0 _
  have hδ : L ^ (-68 : ℤ) ≤ (1 / 4 : ℝ) := by
    rw [show (-68 : ℤ) = -(68 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hL68
  have hP4 : 4 ≤ lemma23PaperP D := by
    have hh := Real.add_one_le_exp (L ^ 9)
    change 4 ≤ Real.exp (L ^ 9)
    linarith only [hh, h512]
  have hP0 : 0 ≤ lemma23PaperP D := (by norm_num : (0 : ℝ) ≤ 4).trans hP4
  have hprod := mul_le_mul_of_nonneg_left hδ hP0
  have hprod0 := mul_nonneg hP0 hδ0
  have hupper : lemma56PrimeUpper D + 1 ≤ 2 * lemma23PaperP D := by
    change lemma23PaperP D * (1 + L ^ (-68 : ℤ)) + 1 ≤ _
    nlinarith only [hprod, hP4]
  have hY0 : 0 ≤ lemma56PrimeUpper D := by
    change 0 ≤ lemma23PaperP D * (1 + L ^ (-68 : ℤ))
    positivity
  refine ⟨?_, hP4, ?_, hupper, ?_⟩
  · rw [lemma23PaperP, Real.log_exp]
    exact (by norm_num : (1 : ℝ) ≤ 512).trans h512
  · change lemma23PaperP D ≤ lemma23PaperP D * (1 + L ^ (-68 : ℤ))
    nlinarith only [hprod0]
  · exact (Nat.ceil_lt_add_one hY0).le.trans hupper

end ZhangLS.Spec
