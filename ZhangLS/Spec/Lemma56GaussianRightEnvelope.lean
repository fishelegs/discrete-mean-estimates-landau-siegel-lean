import ZhangLS.Spec.Lemma56TwistedGaussianLeftBound

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open scoped ComplexOrder

noncomputable def lemma56GaussianRightConstant : ℝ :=
  (LSeries (lemma55MangoldtTwist lemma55ZetaTrivialCharacter) (2 : ℂ)).re

lemma lemma56_actual_logDeriv_two_uniform_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 2) :
    ‖logDeriv (DirichletCharacter.LFunction θ) s‖ ≤ lemma56GaussianRightConstant := by
  let f := lemma55MangoldtTwist lemma55ZetaTrivialCharacter
  have hf : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    rw [show f n = (ArithmeticFunction.vonMangoldt n : ℂ) by exact lemma55_mangoldt_trivial n]
    exact Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg
  have hcoeff (n : ℕ) : ‖lemma56Mangoldt θ n‖ ≤ (f n).re := by
    rw [show f n = (ArithmeticFunction.vonMangoldt n : ℂ) by exact lemma55_mangoldt_trivial n]
    simp only [lemma56Mangoldt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_re]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (θ.norm_le_one _)
      ArithmeticFunction.vonMangoldt_nonneg
  have hfs := lemma55_actual_mangoldt_twist_summable lemma55ZetaTrivialCharacter
    (z := (2 : ℂ)) (by norm_num)
  have hθs := DirichletCharacter.LSeriesSummable_twist_vonMangoldt θ
    (s := lemma55JensenCenter s.im) (by simp)
  have hb := lemma56_nonnegative_majorant_series_bound hf hcoeff hfs s.im hθs
  have he : s = lemma55JensenCenter s.im := by
    apply Complex.ext
    · simpa [lemma55JensenCenter] using hs
    · simp [lemma55JensenCenter]
  rw [lemma56_actual_logDeriv_mangoldt θ (by rw [hs]; norm_num), norm_neg, he]
  exact hb

lemma lemma56_gaussian_right_constant_nonneg : 0 ≤ lemma56GaussianRightConstant := by
  have hb := lemma56_actual_logDeriv_two_uniform_bound (1 : DirichletCharacter ℂ 1)
    (s := 2) (by norm_num)
  exact (norm_nonneg _).trans hb

lemma lemma56_actual_twisted_gaussian_right_envelope {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ t : ℝ) :
    ‖lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I)‖ ≤
      (lemma56GaussianRightConstant * x ^ 2 * (Real.sqrt Real.pi / B) *
        Real.exp (1 / B ^ 2)) * Real.exp (-(1 / (4 * B ^ 2)) * t ^ 2) := by
  have hLD := lemma56_actual_logDeriv_two_uniform_bound θ
    (s := (2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I) (by simp)
  have hn : ‖lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I)‖ =
      ‖logDeriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ *
        ‖lemma56GaussianKernel B 2 x t‖ := by
    have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    simp only [lemma56TwistedGaussianArithmeticIntegrand, lemma56GaussianKernel,
      norm_mul, norm_neg, mul_assoc, htwo]
  rw [hn, lemma56_gaussian_kernel_norm hB hx]
  have he : (2 : ℝ) ^ 2 / (4 * B ^ 2) = 1 / B ^ 2 := by ring
  norm_num only [Real.rpow_natCast, Nat.cast_ofNat] at *
  rw [he]
  simp only [Real.rpow_two]
  let C := x ^ 2 * (Real.sqrt Real.pi / B) * Real.exp (1 / B ^ 2) *
    Real.exp (-(1 / (4 * B ^ 2)) * t ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  convert mul_le_mul_of_nonneg_right hLD hC using 1 <;> dsimp [C] <;> ring


end ZhangLS.Spec
