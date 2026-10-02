import ZhangLS.Spec.Lemma56PerronHorizontal

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_supergaussian_budget {U : ℝ} (hU : 2000 ≤ U) :
    U ^ 2 + 4 * U + 2 ≤ Real.exp U / 16 := by
  have hU0 : 0 ≤ U := by linarith only [hU]
  have he := Real.add_one_le_exp (U / 4)
  have hle : U / 4 ≤ Real.exp (U / 4) := by linarith only [he]
  have hpow : (U / 4) ^ 4 ≤ (Real.exp (U / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hle 4
  have hpe : (Real.exp (U / 4)) ^ 4 = Real.exp U := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpe] at hpow
  have hpoly : U ^ 4 ≤ 256 * Real.exp U := by nlinarith only [hpow]
  have hsq : 4000000 ≤ U ^ 2 := by nlinarith only [hU]
  have hfour : 4000000 * U ^ 2 ≤ U ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg U)
    nlinarith only [hh]
  have hU2 : U ≤ U ^ 2 := by nlinarith only [hU]
  have hsmall : 4096 * (U ^ 2 + 4 * U + 2) ≤ 4000000 * U ^ 2 := by
    nlinarith only [hU2, hsq]
  linarith only [hsmall, hfour, hpoly]

lemma lemma56_perron_paper_scales {U : ℝ} (hU : 0 ≤ U) :
    let B := Real.exp ((3 / 2 : ℝ) * U)
    let H := Real.exp (2 * U) / 2
    1 ≤ B ∧ 0 < H ∧ B ^ 2 / H = 2 * Real.exp U ∧
      H ^ 2 / (4 * B ^ 2) = Real.exp U / 16 ∧ 1 / B ^ 2 ≤ 1 := by
  let B := Real.exp ((3 / 2 : ℝ) * U)
  let H := Real.exp (2 * U) / 2
  have hB : 1 ≤ B := Real.one_le_exp (by positivity)
  have hH : 0 < H := by dsimp [H]; positivity
  have hB2 : B ^ 2 = Real.exp (3 * U) := by
    dsimp [B]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hH2 : H ^ 2 = Real.exp (4 * U) / 4 := by
    dsimp [H]
    rw [div_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
    congr 1
    congr 1
    ring
  have h3 : Real.exp (3 * U) = Real.exp U * Real.exp (2 * U) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (4 * U) = Real.exp U * Real.exp (3 * U) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨hB, hH, ?_, ?_, ?_⟩
  · change B ^ 2 / H = _
    dsimp [H]
    rw [hB2, h3]
    field_simp
  · rw [hH2, hB2, h4]
    field_simp
    norm_num
  · have hs : 1 ≤ B ^ 2 := by nlinarith only [hB]
    change 1 / B ^ 2 ≤ 1
    apply (div_le_iff₀ (sq_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hB))).mpr
    simpa only [one_mul] using hs

lemma lemma56_perron_paper_right_budget {U C x : ℝ} (hU : 2000 ≤ U)
    (hC : 0 ≤ C) (hx : 0 < x) (hxmax : x ≤ 2 * Real.exp (U ^ 2)) :
    let B := Real.exp ((3 / 2 : ℝ) * U)
    let H := Real.exp (2 * U) / 2
    4 * C * x ^ 2 * (B ^ 2 / H) * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) ≤
      32 * C * Real.exp (U ^ 2) * Real.exp (-3 * U) := by
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hs := lemma56_perron_paper_scales hU0
  have hb := lemma56_perron_supergaussian_budget hU
  let B := Real.exp ((3 / 2 : ℝ) * U)
  let H := Real.exp (2 * U) / 2
  have hx2 : x ^ 2 ≤ 4 * (Real.exp (U ^ 2)) ^ 2 := by
    nlinarith only [hx.le, hxmax]
  have hex : Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) ≤
      Real.exp (1 - Real.exp U / 16) := by
    apply Real.exp_le_exp.mpr
    rw [hs.2.2.2.1]
    linarith only [hs.2.2.2.2]
  have hbudget : 2 * U ^ 2 + U + 1 - Real.exp U / 16 ≤ U ^ 2 - 3 * U := by
    linarith only [hb]
  change 4 * C * x ^ 2 * (B ^ 2 / H) * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) ≤ _
  rw [hs.2.2.1]
  calc
    _ ≤ (4 * C * (4 * (Real.exp (U ^ 2)) ^ 2) * (2 * Real.exp U)) *
        Real.exp (1 - Real.exp U / 16) := by gcongr
    _ = 32 * C * Real.exp (2 * U ^ 2 + U + 1 - Real.exp U / 16) := by
      rw [show (Real.exp (U ^ 2)) ^ 2 = Real.exp (2 * U ^ 2) by
        rw [← Real.exp_nat_mul]; norm_num]
      rw [show 2 * U ^ 2 + U + 1 - Real.exp U / 16 =
        (2 * U ^ 2 + U) + (1 - Real.exp U / 16) by ring, Real.exp_add,
        Real.exp_add]
      ring
    _ ≤ 32 * C * Real.exp (U ^ 2 - 3 * U) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbudget) (by positivity)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

end ZhangLS.Spec
