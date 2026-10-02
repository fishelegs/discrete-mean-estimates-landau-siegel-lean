import ZhangLS.Spec.Lemma56ActualPrimeMassScales

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Finset Filter
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_paper_prime_log_interval {D : ℕ} (hP : 0 ≤ lemma23PaperP D) :
    lemma56PaperPrimeLogMass D =
      ∑ n ∈ Ico (⌊lemma23PaperP D⌋₊ + 1) ⌈lemma56PrimeUpper D⌉₊,
        if n.Prime then Real.log (n : ℝ) else 0 := by
  unfold lemma56PaperPrimeLogMass lemma56PaperPrimes
  rw [sum_filter]
  have hsub : Ico (⌊lemma23PaperP D⌋₊ + 1) ⌈lemma56PrimeUpper D⌉₊ ⊆
      range ⌈lemma56PrimeUpper D⌉₊ := by
    intro n hn
    exact mem_range.mpr (mem_Ico.mp hn).2
  rw [← sum_subset hsub]
  · apply sum_congr rfl
    intro n hn
    have hh := mem_Ico.mp hn
    have hlo : lemma23PaperP D < (n : ℝ) := (Nat.floor_lt hP).mp (by omega)
    have hhi : (n : ℝ) < lemma56PrimeUpper D := Nat.lt_ceil.mp hh.2
    simp only [hlo, hhi, and_true]
  · intro n hn hnnot
    by_cases hwindow : n.Prime ∧ lemma23PaperP D < (n : ℝ) ∧ (n : ℝ) < lemma56PrimeUpper D
    · have hh : n ∈ Ico (⌊lemma23PaperP D⌋₊ + 1) ⌈lemma56PrimeUpper D⌉₊ := by
        apply mem_Ico.mpr
        refine ⟨?_, Nat.lt_ceil.mpr hwindow.2.2⟩
        have hlo := (Nat.floor_lt hP).mpr hwindow.2.1
        omega
      exact False.elim (hnnot hh)
    · exact if_neg hwindow

lemma lemma56_actual_prime_log_mass_prefix_difference {D : ℕ}
    (hL : 10000000 ≤ lemma23PaperL D) :
    (lemma56PaperPrimeLogMass D : ℂ) =
      lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) (lemma56PrimeUpper D) 0 -
        lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) (lemma56PaperPrimeLowerCut D) 0 := by
  have hp := lemma56_paper_prime_mass_cut_parameters hL
  have hP : 0 ≤ lemma23PaperP D := (Real.exp_pos _).le
  have hmn : ⌊lemma23PaperP D⌋₊ + 1 ≤ ⌈lemma56PrimeUpper D⌉₊ := by
    have hh : (((⌊lemma23PaperP D⌋₊ + 1 : ℕ) : ℝ)) ≤ (⌈lemma56PrimeUpper D⌉₊ : ℝ) :=
      hp.2.2.2.2.1.trans (Nat.le_ceil _)
    exact_mod_cast hh
  rw [lemma56_actual_paper_prime_log_interval hP, lemma56SharpPrimeLogSum, lemma56SharpPrimeLogSum]
  simp only [ofReal_zero, zero_mul, Complex.cpow_zero, lemma56_principal_one_apply_nat, one_mul,
    lemma56PaperPrimeLowerCut, Nat.ceil_natCast]
  rw [Complex.ofReal_sum]
  simp only [apply_ite, ofReal_zero]
  exact sum_Ico_eq_sub (fun n : ℕ => if n.Prime then (Real.log (n : ℝ) : ℂ) else 0) hmn

end ZhangLS.Spec
