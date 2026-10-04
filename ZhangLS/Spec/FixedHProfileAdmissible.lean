import ZhangLS.Spec.FixedHProfileSequence
import ZhangLS.Spec.Lemma81FiniteZerosReflection

/-! Admission of the actual fixed-H sequence to the original strict P7 cutoff. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHProfile
open Set Function Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma paperP_gt_one {D : ℕ} (hL : 3 ≤ lemma23PaperL D) : 1 < lemma23PaperP D := by
  exact Real.one_lt_exp_iff.mpr (pow_pos (by linarith : 0 < lemma23PaperL D) 9)

lemma upper_window_le_paper_cutoff {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    Real.exp ((201 / 400) * Real.log (lemma23PaperP D)) ≤ lemma81Cutoff D := by
  let L := lemma23PaperL D
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have ht : L ^ (11 / 10 : ℝ) ≤ L ^ 2 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hL1
      (by norm_num : (11 / 10 : ℝ) ≤ (2 : ℕ))
  have h7 : 9 ≤ L ^ 7 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 7
    change 9 ≤ (lemma23PaperL D) ^ 7
    norm_num at hp
    linarith
  have h9 : 9 * L ^ 2 ≤ L ^ 9 := by
    calc
      _ ≤ L ^ 7 * L ^ 2 := mul_le_mul_of_nonneg_right h7 (sq_nonneg L)
      _ = _ := by ring
  have hbudget : (201 / 400) * L ^ 9 ≤ L ^ 9 - 2 * L ^ (11 / 10 : ℝ) := by
    linarith [sq_nonneg L]
  have he : (Real.exp (L ^ (11 / 10 : ℝ))) ^ (-2 : ℤ) =
      Real.exp (-2 * L ^ (11 / 10 : ℝ)) := by
    rw [zpow_neg, zpow_ofNat, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  unfold lemma81Cutoff lemma23PaperP lemma56PaperT
  rw [Real.log_exp]
  change Real.exp ((201 / 400) * L ^ 9) ≤ Real.exp (L ^ 9) *
    Real.exp (L ^ (11 / 10 : ℝ)) ^ (-2 : ℤ)
  rw [he, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [hbudget])

lemma h_paper_admissible {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) :
    Lemma81AdmissibleSequence D 1 (h χ (lemma23PaperP D)) := by
  refine ⟨h_norm_le_one χ _, ?_⟩
  intro n hn
  exact h_eq_zero_of_above χ (paperP_gt_one hL)
    ((upper_window_le_paper_cutoff hL).trans hn)

/-- A uniform modulus threshold, with no character or small-L assumption. -/
lemma h_paper_admissible_eventually : ∃ D₀ : ℕ, 2 ≤ D₀ ∧
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      Lemma81AdmissibleSequence D 1 (h χ (lemma23PaperP D)) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (3 : ℝ)))
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro D hD χ
  exact h_paper_admissible χ (hN D ((le_max_left _ _).trans hD))

end ZhangLS.Spec.FixedHProfile
