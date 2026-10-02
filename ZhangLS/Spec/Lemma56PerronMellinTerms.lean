import ZhangLS.Spec.Lemma56PerronKernel

/-! # Actual oscillatory Perron series terms and absolute convergence -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PerronMellinTerm {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x τ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  lemma56GaussianPhase τ n * LSeries.term (lemma56Mangoldt θ) ((2 : ℂ) + (t : ℂ) * I) n *
    lemma56PerronKernel B 2 x t

noncomputable def lemma56PerronMangoldtTerm {q : ℕ}
    (θ : DirichletCharacter ℂ q) (B x τ : ℝ) (n : ℕ) : ℂ :=
  lemma56GaussianPhase τ n * lemma56Mangoldt θ n * (lemma56PerronWeight B (x / (n : ℝ)) : ℂ)

noncomputable def lemma56PerronMangoldtSum {q : ℕ}
    (θ : DirichletCharacter ℂ q) (B x τ : ℝ) : ℂ :=
  ∑' n : ℕ, lemma56PerronMangoldtTerm θ B x τ n

lemma lemma56_perron_kernel_norm_two {B x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖lemma56PerronKernel B 2 x t‖ = x ^ 2 * ‖lemma56PerronKernel B 2 1 t‖ := by
  unfold lemma56PerronKernel
  rw [norm_div, norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num
  ring

lemma lemma56_perron_mellin_term_norm {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B τ : ℝ) {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖lemma56PerronMellinTerm θ B x τ n t‖ =
      (x ^ 2 * ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖) *
        ‖lemma56PerronKernel B 2 1 t‖ := by
  by_cases hn : n = 0
  · subst n
    simp [lemma56PerronMellinTerm]
  have hterm : ‖LSeries.term (lemma56Mangoldt θ) ((2 : ℂ) + (t : ℂ) * I) n‖ =
      ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    norm_num
  rw [lemma56PerronMellinTerm, norm_mul, norm_mul,
    lemma56_gaussian_phase_norm hn τ, one_mul, hterm, lemma56_perron_kernel_norm_two hx]
  ring

lemma lemma56_perron_mellin_term_eq_kernel {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B τ : ℝ) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    lemma56PerronMellinTerm θ B x τ n t =
      (lemma56GaussianPhase τ n * lemma56Mangoldt θ n) *
        lemma56PerronKernel B 2 (x / (n : ℝ)) t := by
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
  rw [lemma56PerronMellinTerm, LSeries.term_of_ne_zero hn]
  unfold lemma56PerronKernel
  rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  change lemma56GaussianPhase τ n * (lemma56Mangoldt θ n / (n : ℂ) ^ s) *
      ((x : ℂ) ^ s * Complex.exp (s ^ 2 / (4 * (B : ℂ) ^ 2)) / s) =
    (lemma56GaussianPhase τ n * lemma56Mangoldt θ n) *
      (((x / (n : ℝ) : ℝ) : ℂ) ^ s * Complex.exp (s ^ 2 / (4 * (B : ℂ) ^ 2)) / s)
  rw [hp]
  ring

lemma lemma56_perron_mellin_term_integrable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x)
    (τ : ℝ) (n : ℕ) : Integrable (lemma56PerronMellinTerm θ B x τ n) := by
  by_cases hn : n = 0
  · subst n
    have he : lemma56PerronMellinTerm θ B x τ 0 = 0 := by
      funext t
      simp [lemma56PerronMellinTerm]
    rw [he]
    exact integrable_zero ℝ ℂ volume
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hi := (lemma56_perron_kernel_integrable hB (by norm_num : (0 : ℝ) < 2)
    (div_pos hx hnp)).const_mul (lemma56GaussianPhase τ n * lemma56Mangoldt θ n)
  apply hi.congr
  filter_upwards [] with t
  exact (lemma56_perron_mellin_term_eq_kernel θ B τ hx hn t).symm

lemma lemma56_perron_mellin_term_integral {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56PerronMellinTerm θ B x τ n t =
      lemma56PerronMangoldtTerm θ B x τ n := by
  by_cases hn : n = 0
  · subst n
    simp [lemma56PerronMellinTerm, lemma56PerronMangoldtTerm, lemma56Mangoldt]
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp_rw [lemma56_perron_mellin_term_eq_kernel θ B τ hx hn, MeasureTheory.integral_const_mul]
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((lemma56GaussianPhase τ n * lemma56Mangoldt θ n) *
        ∫ t : ℝ, lemma56PerronKernel B 2 (x / (n : ℝ)) t) =
      (lemma56GaussianPhase τ n * lemma56Mangoldt θ n) *
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, lemma56PerronKernel B 2 (x / (n : ℝ)) t) by ring]
  rw [lemma56_perron_kernel_integral hB (by norm_num : (0 : ℝ) < 2) (div_pos hx hnp)]
  rfl

lemma lemma56_perron_mellin_integral_norm_summable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B τ : ℝ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖lemma56PerronMellinTerm θ B x τ n t‖) := by
  have hs : Summable (fun n : ℕ => ‖LSeries.term (lemma56Mangoldt θ) (2 : ℂ) n‖) :=
    summable_norm_iff.mpr (lemma56_actual_mangoldt_summable_two θ)
  let C := x ^ 2 * ∫ t : ℝ, ‖lemma56PerronKernel B 2 1 t‖
  apply (hs.mul_left C).congr
  intro n
  simp_rw [lemma56_perron_mellin_term_norm θ B τ hx n]
  rw [MeasureTheory.integral_const_mul]
  dsimp [C]
  ring

end ZhangLS.Spec
