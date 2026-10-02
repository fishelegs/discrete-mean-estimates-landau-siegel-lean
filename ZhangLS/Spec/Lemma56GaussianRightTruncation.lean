import ZhangLS.Spec.Lemma56GaussianRightEnvelope
import ZhangLS.Spec.Lemma44GaussianVerticalTail

/-! # Actual Gaussian right-line truncation, including both infinite tails -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_twisted_gaussian_right_eq {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x τ t : ℝ) :
    lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I) =
      -(logDeriv (DirichletCharacter.LFunction θ)
        ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56GaussianKernel B 2 x t := by
  have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  simp only [lemma56TwistedGaussianArithmeticIntegrand, lemma56GaussianKernel,
    htwo, mul_assoc]

lemma lemma56_actual_twisted_gaussian_right_integrable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    Integrable (fun t : ℝ => lemma56TwistedGaussianArithmeticIntegrand θ B x τ
      ((2 : ℂ) + (t : ℂ) * I)) := by
  simpa only [lemma56_actual_twisted_gaussian_right_eq] using
    lemma56_actual_twisted_gaussian_mellin_integrable θ hB hx τ

theorem lemma56_actual_twisted_gaussian_right_truncation {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x H : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hH : 0 < H) (τ : ℝ) :
    ‖(∫ t : ℝ, lemma56TwistedGaussianArithmeticIntegrand θ B x τ
        ((2 : ℂ) + (t : ℂ) * I)) -
      (∫ t : ℝ in -H..H, lemma56TwistedGaussianArithmeticIntegrand θ B x τ
        ((2 : ℂ) + (t : ℂ) * I))‖ ≤
      8 * lemma56GaussianRightConstant * x ^ 2 * Real.sqrt Real.pi * (B / H) *
        Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) := by
  let C := lemma56GaussianRightConstant * x ^ 2 * (Real.sqrt Real.pi / B) *
    Real.exp (1 / B ^ 2)
  let b := 1 / (4 * B ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg lemma56_gaussian_right_constant_nonneg
      (sq_nonneg _)) (by positivity)) (Real.exp_nonneg _)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbound := lemma44_gaussian_integral_truncation
    (fun t : ℝ => lemma56TwistedGaussianArithmeticIntegrand θ B x τ
      ((2 : ℂ) + (t : ℂ) * I))
    (lemma56_actual_twisted_gaussian_right_integrable θ hB hx τ) hC hb hH
    (fun t => lemma56_actual_twisted_gaussian_right_envelope θ hB hx τ t)
  apply hbound.trans_eq
  dsimp [C, b]
  rw [show -(1 / (4 * B ^ 2)) * H ^ 2 = -(H ^ 2 / (4 * B ^ 2)) by ring,
    show 1 / B ^ 2 - H ^ 2 / (4 * B ^ 2) =
      1 / B ^ 2 + -(H ^ 2 / (4 * B ^ 2)) by ring, Real.exp_add]
  field_simp
  ring

theorem lemma56_actual_twisted_gaussian_mangoldt_truncation {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x H : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hH : 0 < H) (τ : ℝ) :
    ‖lemma56TwistedGaussianMangoldtSum θ B x τ -
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ in -H..H, lemma56TwistedGaussianArithmeticIntegrand θ B x τ
          ((2 : ℂ) + (t : ℂ) * I))‖ ≤
      (1 / (2 * Real.pi)) *
        (8 * lemma56GaussianRightConstant * x ^ 2 * Real.sqrt Real.pi * (B / H) *
          Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2))) := by
  have hi := lemma56_actual_twisted_gaussian_mellin_identity θ hB hx τ
  simp_rw [← lemma56_actual_twisted_gaussian_right_eq θ B x τ] at hi
  rw [← hi, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left (lemma56_actual_twisted_gaussian_right_truncation θ hB hx hH τ)
    (by positivity)

end ZhangLS.Spec
