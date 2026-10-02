import ZhangLS.Spec.Lemma56PerronMarginBudget

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_perron_right_eq {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x τ t : ℝ) :
    lemma56PerronArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I) =
      -(logDeriv (DirichletCharacter.LFunction θ)
        ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56PerronKernel B 2 x t := by
  simp only [lemma56PerronArithmeticIntegrand, lemma56PerronKernel]
  norm_num

lemma lemma56_actual_perron_right_integrable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    Integrable (fun t : ℝ => lemma56PerronArithmeticIntegrand θ B x τ
      ((2 : ℂ) + (t : ℂ) * I)) := by
  simpa only [lemma56_actual_perron_right_eq] using
    lemma56_actual_perron_mellin_integrable θ hB hx τ

lemma lemma56_actual_perron_right_envelope {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ t : ℝ) :
    ‖lemma56PerronArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I)‖ ≤
      (lemma56GaussianRightConstant * x ^ 2 / 2 * Real.exp (1 / B ^ 2)) *
        Real.exp (-(1 / (4 * B ^ 2)) * t ^ 2) := by
  let z : ℂ := 2 + (t : ℂ) * I
  have hn : 2 ≤ ‖z‖ := by simpa [z] using Complex.re_le_norm z
  have he : (4 - t ^ 2) / (4 * B ^ 2) =
      1 / B ^ 2 + -(1 / (4 * B ^ 2)) * t ^ 2 := by ring
  rw [lemma56_actual_perron_right_eq, norm_mul, norm_neg,
    lemma56_perron_kernel_norm hx, show ((2 : ℝ) ^ 2) = 4 by norm_num, he, Real.exp_add]
  rw [Real.rpow_two]
  calc
    _ ≤ lemma56GaussianRightConstant * (x ^ 2 *
        (Real.exp (1 / B ^ 2) * Real.exp (-(1 / (4 * B ^ 2)) * t ^ 2)) / 2) := by
      apply mul_le_mul
      · exact lemma56_actual_logDeriv_two_uniform_bound θ (by simp)
      · exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hn
      · positivity
      · exact lemma56_gaussian_right_constant_nonneg
    _ = _ := by ring

theorem lemma56_actual_perron_right_truncation {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x H : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hH : 0 < H) (τ : ℝ) :
    ‖(∫ t : ℝ, lemma56PerronArithmeticIntegrand θ B x τ
        ((2 : ℂ) + (t : ℂ) * I)) -
      (∫ t : ℝ in -H..H, lemma56PerronArithmeticIntegrand θ B x τ
        ((2 : ℂ) + (t : ℂ) * I))‖ ≤
      4 * lemma56GaussianRightConstant * x ^ 2 * (B ^ 2 / H) *
        Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) := by
  let C := lemma56GaussianRightConstant * x ^ 2 / 2 * Real.exp (1 / B ^ 2)
  let b := 1 / (4 * B ^ 2)
  have hCr := lemma56_gaussian_right_constant_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hbound := lemma44_gaussian_integral_truncation
    (fun t : ℝ => lemma56PerronArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I))
    (lemma56_actual_perron_right_integrable θ hB hx τ) hC hb hH
    (fun t => lemma56_actual_perron_right_envelope θ hB hx τ t)
  apply hbound.trans_eq
  dsimp [C, b]
  rw [show -(1 / (4 * B ^ 2)) * H ^ 2 = -(H ^ 2 / (4 * B ^ 2)) by ring,
    show 1 / B ^ 2 - H ^ 2 / (4 * B ^ 2) =
      1 / B ^ 2 + -(H ^ 2 / (4 * B ^ 2)) by ring, Real.exp_add]
  field_simp

theorem lemma56_actual_perron_mangoldt_truncation {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x H : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hH : 0 < H) (τ : ℝ) :
    ‖lemma56PerronMangoldtSum θ B x τ -
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ in -H..H, lemma56PerronArithmeticIntegrand θ B x τ
          ((2 : ℂ) + (t : ℂ) * I))‖ ≤
      (1 / (2 * Real.pi)) *
        (4 * lemma56GaussianRightConstant * x ^ 2 * (B ^ 2 / H) *
          Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2))) := by
  have hi := lemma56_actual_perron_mellin_identity θ hB hx τ
  simp_rw [← lemma56_actual_perron_right_eq θ B x τ] at hi
  rw [← hi, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left (lemma56_actual_perron_right_truncation θ hB hx hH τ)
    (by positivity)

end ZhangLS.Spec
