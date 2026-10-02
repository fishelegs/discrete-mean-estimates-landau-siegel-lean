import ZhangLS.Spec.Lemma56GaussianMellinTerms

/-! # Exact actual Gaussian Mangoldt inverse Mellin identity

Absolute convergence justifies the genuine series/integral interchange.
The arithmetic weight is the actual real Gaussian at log(x/n).
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000

noncomputable def lemma56GaussianMangoldtTerm {q : ℕ}
    (θ : DirichletCharacter ℂ q) (B x : ℝ) (n : ℕ) : ℂ :=
  lemma56Mangoldt θ n * (lemma56GaussianWeight B (x / (n : ℝ)) : ℂ)

noncomputable def lemma56GaussianMangoldtSum {q : ℕ}
    (θ : DirichletCharacter ℂ q) (B x : ℝ) : ℂ :=
  ∑' n : ℕ, lemma56GaussianMangoldtTerm θ B x n

theorem lemma56_gaussian_mellin_term_eq_kernel {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B : ℝ) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    lemma56GaussianMellinTerm θ B x n t =
      lemma56Mangoldt θ n * lemma56GaussianKernel B 2 (x / (n : ℝ)) t := by
  let s : ℂ := 2 + (t : ℂ) * I
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have hp : ((x / (n : ℝ) : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (n : ℂ) ^ s := by
    apply (eq_div_iff (Complex.cpow_ne_zero_iff.mpr (.inl hnC))).mpr
    rw [hncast]
    have he := Complex.mul_cpow_ofReal_nonneg (div_pos hx hnp).le hnp.le s
    have hb : ((x / (n : ℝ) : ℝ) : ℂ) * ((n : ℝ) : ℂ) = (x : ℂ) := by
      norm_cast
      field_simp
    rw [← he, hb]
  rw [lemma56GaussianMellinTerm, LSeries.term_of_ne_zero hn]
  unfold lemma56GaussianKernel
  rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  change lemma56Mangoldt θ n / (n : ℂ) ^ s *
      ((x : ℂ) ^ s * lemma56GaussianOmega B s) =
    lemma56Mangoldt θ n * (((x / (n : ℝ) : ℝ) : ℂ) ^ s * lemma56GaussianOmega B s)
  rw [hp]
  ring

theorem lemma56_gaussian_mellin_term_integral {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56GaussianMellinTerm θ B x n t =
      lemma56GaussianMangoldtTerm θ B x n := by
  by_cases hn : n = 0
  · subst n
    simp [lemma56GaussianMellinTerm, lemma56GaussianMangoldtTerm, lemma56Mangoldt]
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp_rw [lemma56_gaussian_mellin_term_eq_kernel θ B hx hn, MeasureTheory.integral_const_mul]
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (lemma56Mangoldt θ n * ∫ t : ℝ, lemma56GaussianKernel B 2 (x / (n : ℝ)) t) =
      lemma56Mangoldt θ n * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, lemma56GaussianKernel B 2 (x / (n : ℝ)) t) by ring]
  rw [lemma56_gaussian_kernel_integral hB 2 (div_pos hx hnp)]
  rfl

theorem lemma56_actual_gaussian_mangoldt_summable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    Summable (lemma56GaussianMangoldtTerm θ B x) := by
  have hs := (MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun n => lemma56_gaussian_mellin_term_integrable θ hB hx n)
    (lemma56_gaussian_mellin_integral_norm_summable θ hB hx)).summable
  exact (hs.mul_left ((1 / (2 * Real.pi) : ℝ) : ℂ)).congr
    (fun n => lemma56_gaussian_mellin_term_integral θ hB hx n)

theorem lemma56_gaussian_mellin_term_tsum {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x t : ℝ) :
    (∑' n : ℕ, lemma56GaussianMellinTerm θ B x n t) =
      -(logDeriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * I)) *
        lemma56GaussianKernel B 2 x t := by
  unfold lemma56GaussianMellinTerm
  rw [tsum_mul_right]
  change LSeries (lemma56Mangoldt θ) ((2 : ℂ) + (t : ℂ) * I) * _ = _
  rw [lemma56_actual_logDeriv_mangoldt θ (by norm_num), neg_neg]

theorem lemma56_actual_gaussian_mellin_integrable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      -(logDeriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * I)) *
        lemma56GaussianKernel B 2 x t) := by
  let A := ∑' n : ℕ, ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖
  let C := x ^ 2 * A
  have hs : Summable (fun n : ℕ => ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖) :=
    summable_norm_iff.mpr (lemma56_actual_mangoldt_summable_two θ)
  have hK := lemma56_gaussian_kernel_integrable hB (2 : ℝ) (x := 1) (by norm_num)
  have hmajor : Integrable (fun t : ℝ => C * ‖lemma56GaussianKernel B 2 1 t‖) := hK.norm.const_mul C
  have hi : Integrable (fun t : ℝ => ∑' n : ℕ, lemma56GaussianMellinTerm θ B x n t) := by
    apply hmajor.mono'
    · exact AEStronglyMeasurable.tsum fun n => (lemma56_gaussian_mellin_term_integrable θ hB hx n).1
    · filter_upwards [] with t
      have hnorm : Summable (fun n : ℕ => ‖lemma56GaussianMellinTerm θ B x n t‖) := by
        apply (hs.mul_left (x ^ 2 * ‖lemma56GaussianKernel B 2 1 t‖)).congr
        intro n
        rw [lemma56_gaussian_mellin_term_norm θ B hx n t]
        ring
      calc
        _ ≤ ∑' n : ℕ, ‖lemma56GaussianMellinTerm θ B x n t‖ := norm_tsum_le_tsum_norm hnorm
        _ = (x ^ 2 * ‖lemma56GaussianKernel B 2 1 t‖) * A := by
          simp_rw [lemma56_gaussian_mellin_term_norm θ B hx]
          dsimp [A]
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          ring
        _ = C * ‖lemma56GaussianKernel B 2 1 t‖ := by dsimp [C]; ring
  simpa only [lemma56_gaussian_mellin_term_tsum] using hi

theorem lemma56_actual_gaussian_mellin_identity {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, -(logDeriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * I)) *
          lemma56GaussianKernel B 2 x t = lemma56GaussianMangoldtSum θ B x := by
  have hi := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => lemma56_gaussian_mellin_term_integrable θ hB hx n)
    (lemma56_gaussian_mellin_integral_norm_summable θ hB hx)
  simp_rw [← lemma56_gaussian_mellin_term_tsum θ B x]
  rw [← hi, ← tsum_mul_left]
  simp_rw [lemma56_gaussian_mellin_term_integral θ hB hx]
  rfl

end ZhangLS.Spec
