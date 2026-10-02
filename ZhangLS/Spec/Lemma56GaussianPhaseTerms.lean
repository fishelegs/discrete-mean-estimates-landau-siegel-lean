import ZhangLS.Spec.Lemma56GaussianContour

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56GaussianPhase (τ : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ ((τ : ℂ) * I)

noncomputable def lemma56TwistedGaussianMellinTerm {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x τ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  lemma56GaussianPhase τ n * lemma56GaussianMellinTerm θ B x n t

noncomputable def lemma56TwistedGaussianMangoldtTerm {q : ℕ}
    (θ : DirichletCharacter ℂ q) (B x τ : ℝ) (n : ℕ) : ℂ :=
  lemma56GaussianPhase τ n * lemma56GaussianMangoldtTerm θ B x n

noncomputable def lemma56TwistedGaussianMangoldtSum {q : ℕ}
    (θ : DirichletCharacter ℂ q) (B x τ : ℝ) : ℂ :=
  ∑' n : ℕ, lemma56TwistedGaussianMangoldtTerm θ B x τ n

lemma lemma56_gaussian_phase_norm {n : ℕ} (hn : n ≠ 0) (τ : ℝ) :
    ‖lemma56GaussianPhase τ n‖ = 1 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold lemma56GaussianPhase
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnp]
  simp

lemma lemma56_gaussian_phase_LSeries_term (f : ℕ → ℂ) (s : ℂ) (τ : ℝ) (n : ℕ) :
    lemma56GaussianPhase τ n * LSeries.term f s n =
      LSeries.term f (s - (τ : ℂ) * I) n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hns : (n : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hnC)
  have hnt : (n : ℂ) ^ ((τ : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hnC)
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_sub _ _ hnC]
  unfold lemma56GaussianPhase
  field_simp

lemma lemma56_twisted_gaussian_mellin_term_norm {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x τ : ℝ) (n : ℕ) (t : ℝ) :
    ‖lemma56TwistedGaussianMellinTerm θ B x τ n t‖ =
      ‖lemma56GaussianMellinTerm θ B x n t‖ := by
  by_cases hn : n = 0
  · subst n
    simp [lemma56TwistedGaussianMellinTerm, lemma56GaussianMellinTerm]
  rw [lemma56TwistedGaussianMellinTerm, norm_mul, lemma56_gaussian_phase_norm hn τ, one_mul]

lemma lemma56_twisted_gaussian_mellin_term_integrable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x)
    (τ : ℝ) (n : ℕ) : Integrable (lemma56TwistedGaussianMellinTerm θ B x τ n) :=
  (lemma56_gaussian_mellin_term_integrable θ hB hx n).const_mul _

lemma lemma56_twisted_gaussian_mellin_integral_norm_summable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖lemma56TwistedGaussianMellinTerm θ B x τ n t‖) := by
  simpa only [lemma56_twisted_gaussian_mellin_term_norm] using
    lemma56_gaussian_mellin_integral_norm_summable θ hB hx

lemma lemma56_twisted_gaussian_mellin_term_integral {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      lemma56TwistedGaussianMellinTerm θ B x τ n t =
        lemma56TwistedGaussianMangoldtTerm θ B x τ n := by
  unfold lemma56TwistedGaussianMellinTerm lemma56TwistedGaussianMangoldtTerm
  rw [MeasureTheory.integral_const_mul]
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (lemma56GaussianPhase τ n * ∫ t : ℝ, lemma56GaussianMellinTerm θ B x n t) =
      lemma56GaussianPhase τ n * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, lemma56GaussianMellinTerm θ B x n t) by ring]
  rw [lemma56_gaussian_mellin_term_integral θ hB hx n]


end ZhangLS.Spec
