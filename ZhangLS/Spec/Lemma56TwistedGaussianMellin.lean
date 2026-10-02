import ZhangLS.Spec.Lemma56GaussianPhaseTerms

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_actual_twisted_gaussian_mangoldt_summable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    Summable (lemma56TwistedGaussianMangoldtTerm θ B x τ) := by
  have hs := (MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun n => lemma56_twisted_gaussian_mellin_term_integrable θ hB hx τ n)
    (lemma56_twisted_gaussian_mellin_integral_norm_summable θ hB hx τ)).summable
  exact (hs.mul_left ((1 / (2 * Real.pi) : ℝ) : ℂ)).congr
    (fun n => lemma56_twisted_gaussian_mellin_term_integral θ hB hx τ n)

lemma lemma56_twisted_gaussian_mellin_term_tsum {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x τ t : ℝ) :
    (∑' n : ℕ, lemma56TwistedGaussianMellinTerm θ B x τ n t) =
      -(logDeriv (DirichletCharacter.LFunction θ)
        ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56GaussianKernel B 2 x t := by
  unfold lemma56TwistedGaussianMellinTerm lemma56GaussianMellinTerm
  simp_rw [← mul_assoc, lemma56_gaussian_phase_LSeries_term]
  rw [tsum_mul_right]
  change LSeries (lemma56Mangoldt θ) ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I) * _ = _
  rw [lemma56_actual_logDeriv_mangoldt θ (by norm_num), neg_neg]

theorem lemma56_actual_twisted_gaussian_mellin_integrable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    Integrable (fun t : ℝ => -(logDeriv (DirichletCharacter.LFunction θ)
      ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56GaussianKernel B 2 x t) := by
  let A := ∑' n : ℕ, ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖
  let C := x ^ 2 * A
  have hs : Summable (fun n : ℕ => ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖) :=
    summable_norm_iff.mpr (lemma56_actual_mangoldt_summable_two θ)
  have hK := lemma56_gaussian_kernel_integrable hB (2 : ℝ) (x := 1) (by norm_num)
  have hmajor : Integrable (fun t : ℝ => C * ‖lemma56GaussianKernel B 2 1 t‖) := hK.norm.const_mul C
  have hi : Integrable (fun t : ℝ => ∑' n : ℕ, lemma56TwistedGaussianMellinTerm θ B x τ n t) := by
    apply hmajor.mono'
    · exact AEStronglyMeasurable.tsum fun n =>
        (lemma56_twisted_gaussian_mellin_term_integrable θ hB hx τ n).1
    · filter_upwards [] with t
      have hnorm : Summable (fun n : ℕ => ‖lemma56TwistedGaussianMellinTerm θ B x τ n t‖) := by
        apply (hs.mul_left (x ^ 2 * ‖lemma56GaussianKernel B 2 1 t‖)).congr
        intro n
        rw [lemma56_twisted_gaussian_mellin_term_norm, lemma56_gaussian_mellin_term_norm θ B hx n t]
        ring
      calc
        _ ≤ ∑' n : ℕ, ‖lemma56TwistedGaussianMellinTerm θ B x τ n t‖ := norm_tsum_le_tsum_norm hnorm
        _ = (x ^ 2 * ‖lemma56GaussianKernel B 2 1 t‖) * A := by
          simp_rw [lemma56_twisted_gaussian_mellin_term_norm, lemma56_gaussian_mellin_term_norm θ B hx]
          dsimp [A]
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          ring
        _ = C * ‖lemma56GaussianKernel B 2 1 t‖ := by dsimp [C]; ring
  simpa only [lemma56_twisted_gaussian_mellin_term_tsum] using hi

theorem lemma56_actual_twisted_gaussian_mellin_identity {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      -(logDeriv (DirichletCharacter.LFunction θ)
        ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56GaussianKernel B 2 x t =
          lemma56TwistedGaussianMangoldtSum θ B x τ := by
  have hi := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => lemma56_twisted_gaussian_mellin_term_integrable θ hB hx τ n)
    (lemma56_twisted_gaussian_mellin_integral_norm_summable θ hB hx τ)
  simp_rw [← lemma56_twisted_gaussian_mellin_term_tsum θ B x τ]
  rw [← hi, ← tsum_mul_left]
  simp_rw [lemma56_twisted_gaussian_mellin_term_integral θ hB hx τ]
  rfl


end ZhangLS.Spec
