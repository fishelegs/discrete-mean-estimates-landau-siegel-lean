import ZhangLS.Spec.Lemma56MangoldtMajorant

/-! # Actual finite strict cutoff and the arithmetic Perron smoothing error -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56SharpMangoldtTerm {q : ℕ} (θ : DirichletCharacter ℂ q)
    (x τ : ℝ) (n : ℕ) : ℂ :=
  if (n : ℝ) < x then lemma56GaussianPhase τ n * lemma56Mangoldt θ n else 0

noncomputable def lemma56SharpMangoldtSum {q : ℕ} (θ : DirichletCharacter ℂ q)
    (x τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈x⌉₊, lemma56GaussianPhase τ n * lemma56Mangoldt θ n

noncomputable def lemma56PerronErrorTerm {q : ℕ} (θ : DirichletCharacter ℂ q)
    (B x τ : ℝ) (n : ℕ) : ℂ :=
  (lemma56GaussianPhase τ n * lemma56Mangoldt θ n) *
    ((lemma56PerronWeight B (x / (n : ℝ)) - (if (n : ℝ) < x then 1 else 0) : ℝ) : ℂ)

lemma lemma56_sharp_mangoldt_term_outside {q : ℕ} (θ : DirichletCharacter ℂ q)
    (x τ : ℝ) {n : ℕ} (hn : n ∉ Finset.range ⌈x⌉₊) :
    lemma56SharpMangoldtTerm θ x τ n = 0 := by
  have hnot : ¬(n : ℝ) < x := by
    intro h
    exact hn (Finset.mem_range.mpr (Nat.lt_ceil.mpr h))
  simp only [lemma56SharpMangoldtTerm, if_neg hnot]

lemma lemma56_sharp_mangoldt_term_summable {q : ℕ} (θ : DirichletCharacter ℂ q) (x τ : ℝ) :
    Summable (lemma56SharpMangoldtTerm θ x τ) :=
  summable_of_ne_finset_zero (s := Finset.range ⌈x⌉₊)
    (fun n hn => lemma56_sharp_mangoldt_term_outside θ x τ hn)

lemma lemma56_sharp_mangoldt_term_tsum {q : ℕ} (θ : DirichletCharacter ℂ q) (x τ : ℝ) :
    (∑' n : ℕ, lemma56SharpMangoldtTerm θ x τ n) = lemma56SharpMangoldtSum θ x τ := by
  rw [tsum_eq_sum (s := Finset.range ⌈x⌉₊)
    (fun n hn => lemma56_sharp_mangoldt_term_outside θ x τ hn)]
  unfold lemma56SharpMangoldtSum
  apply Finset.sum_congr rfl
  intro n hn
  have hx := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
  simp only [lemma56SharpMangoldtTerm, if_pos hx]

lemma lemma56_perron_error_term_eq_sub {q : ℕ} (θ : DirichletCharacter ℂ q)
    (B x τ : ℝ) (n : ℕ) :
    lemma56PerronErrorTerm θ B x τ n =
      lemma56PerronMangoldtTerm θ B x τ n - lemma56SharpMangoldtTerm θ x τ n := by
  by_cases h : (n : ℝ) < x
  · simp only [lemma56PerronErrorTerm, lemma56PerronMangoldtTerm,
      lemma56SharpMangoldtTerm, if_pos h, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  · simp only [lemma56PerronErrorTerm, lemma56PerronMangoldtTerm,
      lemma56SharpMangoldtTerm, if_neg h, sub_zero]

lemma lemma56_perron_error_term_summable {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    Summable (lemma56PerronErrorTerm θ B x τ) := by
  have hs := (lemma56_actual_perron_mangoldt_summable θ hB hx τ).sub
    (lemma56_sharp_mangoldt_term_summable θ x τ)
  exact hs.congr (fun n => (lemma56_perron_error_term_eq_sub θ B x τ n).symm)

lemma lemma56_perron_error_term_tsum {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    (∑' n : ℕ, lemma56PerronErrorTerm θ B x τ n) =
      lemma56PerronMangoldtSum θ B x τ - lemma56SharpMangoldtSum θ x τ := by
  simp_rw [lemma56_perron_error_term_eq_sub]
  rw [(lemma56_actual_perron_mangoldt_summable θ hB hx τ).tsum_sub
    (lemma56_sharp_mangoldt_term_summable θ x τ), lemma56_sharp_mangoldt_term_tsum]
  rfl

lemma lemma56_perron_error_zero {q : ℕ} (θ : DirichletCharacter ℂ q) (B x τ : ℝ) :
    lemma56PerronErrorTerm θ B x τ 0 = 0 := by
  simp [lemma56PerronErrorTerm, lemma56Mangoldt]

lemma lemma56_perron_error_distance_majorant {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x ε : ℝ} (hB : 0 < B) (hx : 0 < x) (hε : 0 ≤ ε) (hwide : 1 ≤ B * ε)
    (τ : ℝ) (n : ℕ) (hdist : ε ≤ |Real.log (x / (n : ℝ))|) :
    ‖lemma56PerronErrorTerm θ B x τ n‖ ≤
      ((Real.sqrt Real.pi)⁻¹ * x ^ 2 * Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2)) *
        lemma56MangoldtMajorant n := by
  by_cases hn : n = 0
  · subst n
    rw [lemma56_perron_error_zero]
    simp [lemma56MangoldtMajorant]
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hy : 0 < x / (n : ℝ) := div_pos hx hnp
  have hw := lemma56_perron_weight_step_error_distance_bound hB hy hε hdist hwide
  have he : (if (n : ℝ) < x then (1 : ℝ) else 0) =
      (if 1 < x / (n : ℝ) then (1 : ℝ) else 0) := by
    simp only [lt_div_iff₀ hnp, one_mul]
  rw [lemma56PerronErrorTerm, norm_mul, norm_mul, lemma56_gaussian_phase_norm hn τ,
    one_mul, Complex.norm_real, Real.norm_eq_abs, he]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n * ((Real.sqrt Real.pi)⁻¹ * (x / (n : ℝ)) ^ 2 *
        Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2)) :=
      mul_le_mul (lemma56_mangoldt_norm_le θ n) hw (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by
      unfold lemma56MangoldtMajorant
      field_simp

end ZhangLS.Spec
