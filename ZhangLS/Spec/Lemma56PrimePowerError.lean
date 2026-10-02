import ZhangLS.Spec.Lemma56SharpMangoldtWindow
import Mathlib.NumberTheory.Chebyshev

/-! # Actual smoothing removal and prime-log estimates for Lemma 5.6

The original prime-window target and its principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56SharpPrimeLogSum {q : ℕ} (θ : DirichletCharacter ℂ q)
    (x τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈x⌉₊, if n.Prime then
    (n : ℂ) ^ ((τ : ℂ) * I) * (θ (n : ZMod q) * (Real.log (n : ℝ) : ℂ)) else 0

lemma lemma56_actual_sharp_prime_power_difference {q : ℕ} (θ : DirichletCharacter ℂ q)
    (x τ : ℝ) :
    lemma56SharpMangoldtSum θ x τ - lemma56SharpPrimeLogSum θ x τ =
      ∑ n ∈ Finset.range ⌈x⌉₊, if ¬n.Prime then
        lemma56GaussianPhase τ n * lemma56Mangoldt θ n else 0 := by
  rw [lemma56SharpMangoldtSum, lemma56SharpPrimeLogSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp only [hp, not_true_eq_false, if_pos, if_false, lemma56GaussianPhase,
      lemma56Mangoldt, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
  · simp only [hp, not_false_eq_true, if_false, if_true, sub_zero, lemma56GaussianPhase]

lemma lemma56_actual_sharp_prime_power_norm {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) (τ : ℝ) :
    ‖lemma56SharpMangoldtSum θ x τ - lemma56SharpPrimeLogSum θ x τ‖ ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  let f : ℕ → ℝ := fun n => if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0
  have hzero : f 0 = 0 := by simp [f]
  have hdrop : (∑ n ∈ Finset.range ⌈x⌉₊, f n) =
      ∑ n ∈ (Finset.range ⌈x⌉₊).erase 0, f n := by
    symm
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro n hn hnnot
    by_cases hn0 : n = 0
    · simpa only [hn0] using hzero
    · exact False.elim (hnnot (Finset.mem_erase.mpr ⟨hn0, hn⟩))
  have hsub : (Finset.range ⌈x⌉₊).erase 0 ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro n hn
    have hh := Finset.mem_erase.mp hn
    have hnx : (n : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hh.2)
    exact Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hh.1,
      (Nat.le_floor_iff (by linarith only [hx] : 0 ≤ x)).mpr hnx.le⟩
  rw [lemma56_actual_sharp_prime_power_difference,
    Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
  calc
    _ ≤ ∑ n ∈ Finset.range ⌈x⌉₊,
        ‖if ¬n.Prime then lemma56GaussianPhase τ n * lemma56Mangoldt θ n else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range ⌈x⌉₊, f n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · simp [hp, f]
      · simp only [hp, not_false_eq_true, if_true, f]
        by_cases hn0 : n = 0
        · subst n
          simp [lemma56Mangoldt]
        · rw [norm_mul, lemma56_gaussian_phase_norm hn0, one_mul]
          exact lemma56_mangoldt_norm_le θ n
    _ = ∑ n ∈ (Finset.range ⌈x⌉₊).erase 0, f n := hdrop
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n hn hnnot
      dsimp [f]
      by_cases hp : n.Prime
      · simp [hp]
      · simp only [hp, not_false_eq_true, if_true]
        exact ArithmeticFunction.vonMangoldt_nonneg

lemma lemma56_actual_sharp_prime_power_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) (τ : ℝ) :
    ‖lemma56SharpMangoldtSum θ x τ - lemma56SharpPrimeLogSum θ x τ‖ ≤
      2 * Real.sqrt x * Real.log x :=
  (lemma56_actual_sharp_prime_power_norm θ hx τ).trans
    (Chebyshev.psi_sub_theta_le hx)

end ZhangLS.Spec
