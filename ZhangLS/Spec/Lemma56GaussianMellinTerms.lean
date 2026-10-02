import ZhangLS.Spec.Lemma56GaussianKernel

/-! # Actual Mangoldt Gaussian series terms and absolute integral bounds

The character may be complex or principal. Absolute convergence on Re s=2
and the proved scalar Gaussian bound justify the arithmetic interchange.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000

noncomputable def lemma56GaussianMellinTerm {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (lemma56Mangoldt θ) ((2 : ℂ) + (t : ℂ) * I) n *
    lemma56GaussianKernel B 2 x t

theorem lemma56_actual_mangoldt_summable_two {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) : LSeriesSummable (lemma56Mangoldt θ) (2 : ℂ) :=
  DirichletCharacter.LSeriesSummable_twist_vonMangoldt θ (by norm_num)

theorem lemma56_gaussian_mellin_term_norm {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B : ℝ) {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖lemma56GaussianMellinTerm θ B x n t‖ =
      (x ^ 2 * ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖) *
        ‖lemma56GaussianKernel B 2 1 t‖ := by
  have hterm : ‖LSeries.term (lemma56Mangoldt θ) ((2 : ℂ) + (t : ℂ) * I) n‖ =
      ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    norm_num
  have hunit : lemma56GaussianKernel B 2 1 t =
      lemma56GaussianOmega B ((2 : ℂ) + (t : ℂ) * I) := by simp [lemma56GaussianKernel]
  rw [lemma56GaussianMellinTerm, norm_mul, hterm, hunit, lemma56GaussianKernel,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num
  ring

theorem lemma56_gaussian_mellin_term_integrable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (n : ℕ) :
    Integrable (lemma56GaussianMellinTerm θ B x n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : lemma56GaussianMellinTerm θ B x 0 = 0 := by
      funext t
      simp [lemma56GaussianMellinTerm]
    rw [hzero]
    exact integrable_zero ℝ ℂ volume
  have hK := lemma56_gaussian_kernel_integrable hB (2 : ℝ) (x := 1) (by norm_num)
  let C := x ^ 2 * ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖
  have hmajor : Integrable (fun t : ℝ => C * ‖lemma56GaussianKernel B 2 1 t‖) := hK.norm.const_mul C
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hz : Continuous (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) := by fun_prop
    have hterm : Continuous (fun t : ℝ =>
        LSeries.term (lemma56Mangoldt θ) ((2 : ℂ) + (t : ℂ) * I) n) := by
      simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div₀ (hz.const_cpow (.inl hnC))
        (fun _ => Complex.cpow_ne_zero_iff.mpr (.inl hnC))
    have hpower : Continuous (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I)) :=
      hz.const_cpow (.inl (ofReal_ne_zero.mpr hx.ne'))
    have hOmega : Continuous (fun t : ℝ => lemma56GaussianOmega B ((2 : ℂ) + (t : ℂ) * I)) := by
      unfold lemma56GaussianOmega
      fun_prop
    exact hterm.mul (hpower.mul hOmega)
  · filter_upwards [] with t
    exact (lemma56_gaussian_mellin_term_norm θ B hx n t).le

theorem lemma56_gaussian_mellin_integral_norm_summable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖lemma56GaussianMellinTerm θ B x n t‖) := by
  have hs : Summable (fun n : ℕ => ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖) :=
    summable_norm_iff.mpr (lemma56_actual_mangoldt_summable_two θ)
  let K := x ^ 2 * ∫ t : ℝ, ‖lemma56GaussianKernel B 2 1 t‖
  apply (hs.mul_left K).congr
  intro n
  simp_rw [lemma56_gaussian_mellin_term_norm θ B hx n]
  rw [MeasureTheory.integral_const_mul]
  dsimp [K]
  ring

end ZhangLS.Spec
