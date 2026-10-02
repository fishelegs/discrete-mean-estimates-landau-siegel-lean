import ZhangLS.Spec.Lemma56PerronWeightDecay

/-! # The actual positive Mangoldt majorant at real part two -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real ComplexOrder
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56MangoldtMajorant (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2

lemma lemma56_mangoldt_majorant_nonneg (n : ℕ) : 0 ≤ lemma56MangoldtMajorant n := by
  unfold lemma56MangoldtMajorant
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)

lemma lemma56_mangoldt_majorant_eq_norm_term (n : ℕ) :
    lemma56MangoldtMajorant n =
      ‖LSeries.term (lemma55MangoldtTwist lemma55ZetaTrivialCharacter) (2 : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [lemma56MangoldtMajorant]
  rw [LSeries.norm_term_eq, if_neg hn, lemma55_mangoldt_trivial]
  norm_num [lemma56MangoldtMajorant, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.rpow_two]

lemma lemma56_mangoldt_majorant_summable : Summable lemma56MangoldtMajorant := by
  have hs := (lemma55_actual_mangoldt_twist_summable lemma55ZetaTrivialCharacter
    (z := (2 : ℂ)) (by norm_num)).norm
  exact hs.congr fun n => (lemma56_mangoldt_majorant_eq_norm_term n).symm

lemma lemma56_mangoldt_majorant_tsum : (∑' n : ℕ, lemma56MangoldtMajorant n) =
    lemma56GaussianRightConstant := by
  let f := lemma55MangoldtTwist lemma55ZetaTrivialCharacter
  have hf (n : ℕ) : 0 ≤ f n := by
    rw [show f n = (ArithmeticFunction.vonMangoldt n : ℂ) by exact lemma55_mangoldt_trivial n]
    exact Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg
  have hs := lemma55_actual_mangoldt_twist_summable lemma55ZetaTrivialCharacter
    (z := (2 : ℂ)) (by norm_num)
  calc
    _ = ∑' n : ℕ, (LSeries.term f (2 : ℂ) n).re := by
      apply tsum_congr
      intro n
      rw [lemma56_mangoldt_majorant_eq_norm_term]
      exact (Complex.re_eq_norm.mpr (LSeries.term_nonneg (hf n) (2 : ℝ))).symm
    _ = (LSeries f (2 : ℂ)).re := (Complex.re_tsum hs).symm
    _ = _ := rfl

lemma lemma56_mangoldt_norm_le {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖lemma56Mangoldt θ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  rw [lemma56Mangoldt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (θ.norm_le_one _)
    ArithmeticFunction.vonMangoldt_nonneg

end ZhangLS.Spec
