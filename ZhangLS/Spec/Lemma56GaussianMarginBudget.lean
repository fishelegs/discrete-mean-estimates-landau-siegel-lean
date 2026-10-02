import ZhangLS.Spec.Lemma56TwistedGaussianVertical

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_paper_power_margin_identity {L : ℝ} (hL : 0 < L) :
    (Real.exp (L ^ 9)) ^ (1 - 1 / ((3 / 4 : ℝ) * L ^ (9 / 2 : ℝ))) =
      Real.exp (L ^ 9) * Real.exp (-((4 / 3 : ℝ) * L ^ (9 / 2 : ℝ))) := by
  have hU : 0 < L ^ (9 / 2 : ℝ) := Real.rpow_pos_of_pos hL _
  have hpow : (L ^ (9 / 2 : ℝ)) ^ 2 = L ^ 9 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
  congr 1
  rw [← hpow]
  field_simp
  ring

lemma lemma56_gaussian_margin_polynomial_absorption {U : ℝ} (hU : 1 ≤ U) :
    (24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U)) *
      Real.exp (-((4 / 3 : ℝ) * U)) ≤
        4150656 * Real.exp (-((7 / 6 : ℝ) * U)) := by
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hM : 24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U) ≤ 28824 * U ^ 2 := by
    have hs : U ≤ U ^ 2 := by nlinarith only [hU]
    nlinarith only [hs, sq_nonneg U]
  have he := Real.add_one_le_exp (U / 12)
  have hle : U / 12 ≤ Real.exp (U / 12) := by linarith only [he]
  have hsq : (U / 12) ^ 2 ≤ (Real.exp (U / 12)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have hsqe : (Real.exp (U / 12)) ^ 2 = Real.exp (U / 6) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsqe] at hsq
  have hpoly : U ^ 2 ≤ 144 * Real.exp (U / 6) := by nlinarith only [hsq]
  calc
    _ ≤ (28824 * (144 * Real.exp (U / 6))) * Real.exp (-((4 / 3 : ℝ) * U)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact hM.trans (mul_le_mul_of_nonneg_left hpoly (by norm_num))
    _ = _ := by
      rw [show (28824 * (144 * Real.exp (U / 6))) * Real.exp (-((4 / 3 : ℝ) * U)) =
        (28824 * 144) * (Real.exp (U / 6) * Real.exp (-((4 / 3 : ℝ) * U))) by ring,
        ← Real.exp_add]
      have heq : U / 6 + -((4 / 3 : ℝ) * U) = -((7 / 6 : ℝ) * U) := by ring
      rw [heq]
      ring

lemma lemma56_paper_left_gaussian_budget {L B : ℝ} (hL : 2000 ≤ L) (hB : 1 ≤ B) :
    let U := L ^ (9 / 2 : ℝ)
    let V := (3 / 4 : ℝ) * U
    let a := 1 - 1 / V
    (24 * V ^ 2 + 28800 * V) * (Real.exp (L ^ 9)) ^ a *
      Real.exp (a ^ 2 / (4 * B ^ 2)) ≤
        (4150656 * Real.exp (1 / 4 : ℝ)) * Real.exp (L ^ 9) *
          Real.exp (-((7 / 6 : ℝ) * U)) := by
  let U := L ^ (9 / 2 : ℝ)
  let V := (3 / 4 : ℝ) * U
  let a := 1 - 1 / V
  have hLp : 0 < L := by linarith only [hL]
  have hs := lemma56_high_scale_strict_margin hL
  have hV1 : 1 ≤ V := by dsimp [V, U]; linarith only [hs.2.2.1]
  have hVp : 0 < V := by linarith only [hV1]
  have hInv : 0 < 1 / V := by positivity
  have hInv1 : 1 / V ≤ 1 := by exact (div_le_iff₀ hVp).mpr (by simpa using hV1)
  have ha : 0 ≤ a ∧ a ≤ 1 := by dsimp [a]; constructor <;> linarith only [hInv, hInv1]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith only [ha.1, ha.2]
  have hB2 : 1 ≤ B ^ 2 := by nlinarith only [hB]
  have hden : 0 < 4 * B ^ 2 := by positivity
  have hratio : a ^ 2 / (4 * B ^ 2) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [ha2, hB2]
  have hU1 : 1 ≤ U := by dsimp [U] at *; linarith only [hs.2.2.1]
  have hp := lemma56_paper_power_margin_identity hLp
  have hm := lemma56_gaussian_margin_polynomial_absorption hU1
  change (24 * V ^ 2 + 28800 * V) * (Real.exp (L ^ 9)) ^ a *
    Real.exp (a ^ 2 / (4 * B ^ 2)) ≤ _
  rw [hp]
  calc
    _ ≤ (Real.exp (L ^ 9) *
        ((24 * V ^ 2 + 28800 * V) * Real.exp (-((4 / 3 : ℝ) * U)))) *
          Real.exp (1 / 4 : ℝ) := by
      have he := Real.exp_le_exp.mpr hratio
      convert mul_le_mul_of_nonneg_left he
        (by positivity : 0 ≤ (24 * V ^ 2 + 28800 * V) *
          (Real.exp (L ^ 9) * Real.exp (-((4 / 3 : ℝ) * U)))) using 1 <;> ring
    _ ≤ (Real.exp (L ^ 9) * (4150656 * Real.exp (-((7 / 6 : ℝ) * U)))) *
          Real.exp (1 / 4 : ℝ) := by gcongr
    _ = _ := by ring


end ZhangLS.Spec
