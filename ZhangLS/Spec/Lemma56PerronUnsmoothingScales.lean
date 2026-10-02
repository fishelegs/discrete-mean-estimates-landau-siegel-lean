import ZhangLS.Spec.Lemma56PerronNearError

/-! # Actual smoothing removal and prime-log estimates for Lemma 5.6

The original prime-window target and its principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_exp_window_bound {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.exp ε - Real.exp (-ε) ≤ 2 * Real.exp 1 * ε := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => Real.exp t) (a := -ε) (b := ε) (C := Real.exp 1) (fun t ht => by
      have hh : t ∈ Set.Ioc (-ε) ε := by
        simpa only [Set.uIoc_of_le (by linarith only [hε0] : -ε ≤ ε)] using ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (hh.2.trans hε1))
  rw [integral_exp, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith only [hε0]))),
    abs_of_nonneg (by linarith only [hε0] : 0 ≤ ε - -ε)] at hb
  convert hb using 1 <;> ring

lemma lemma56_perron_unsmoothing_scales {U : ℝ} (hU : 0 ≤ U) :
    let B := Real.exp ((3 / 2 : ℝ) * U)
    let ε := Real.exp (-((7 / 5 : ℝ) * U))
    0 < B ∧ 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ B * ε ∧
      B ^ 2 * ε ^ 2 = Real.exp (U / 5) ∧ 2 / B ^ 2 ≤ 2 := by
  let B := Real.exp ((3 / 2 : ℝ) * U)
  let ε := Real.exp (-((7 / 5 : ℝ) * U))
  have hB : 0 < B := Real.exp_pos _
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hU])
  have hB1 : 1 ≤ B := Real.one_le_exp (by positivity)
  have he : B * ε = Real.exp (U / 10) := by
    dsimp [B, ε]
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨hB, hε, hε1, ?_, ?_, ?_⟩
  · rw [he]
    exact Real.one_le_exp (by positivity)
  · rw [← mul_pow, he, ← Real.exp_nat_mul]
    congr 1
    ring
  · have hsq : 1 ≤ B ^ 2 := by nlinarith only [hB1]
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    nlinarith only [hsq]

lemma lemma56_perron_unsmoothing_far_margin {U : ℝ} (hU : 2000 ≤ U) :
    U ^ 2 + 3 * U + 3 ≤ Real.exp (U / 5) / 2 := by
  have hU0 : 0 ≤ U := by linarith only [hU]
  have he := Real.add_one_le_exp (U / 20)
  have hle : U / 20 ≤ Real.exp (U / 20) := by linarith only [he]
  have hp : (U / 20) ^ 4 ≤ (Real.exp (U / 20)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hle 4
  have hpe : (Real.exp (U / 20)) ^ 4 = Real.exp (U / 5) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpe] at hp
  have hpoly : U ^ 4 ≤ 160000 * Real.exp (U / 5) := by nlinarith only [hp]
  have hsq : 4000000 ≤ U ^ 2 := by nlinarith only [hU]
  have hfour : 4000000 * U ^ 2 ≤ U ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg U)
    nlinarith only [hh]
  have hU2 : U ≤ U ^ 2 := by nlinarith only [hU]
  have hsmall : 320000 * (U ^ 2 + 3 * U + 3) ≤ 4000000 * U ^ 2 := by
    nlinarith only [hU2, hsq]
  linarith only [hsmall, hfour, hpoly]

end ZhangLS.Spec
