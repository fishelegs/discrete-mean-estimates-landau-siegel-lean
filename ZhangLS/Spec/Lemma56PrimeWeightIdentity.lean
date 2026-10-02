import ZhangLS.Spec.Lemma56FiniteAbelBudget

/-! # Actual finite Abel conversion for original Lemma 5.6

Actual prime-mass normalization and the faithful principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_prime_weight_identity {q p : ℕ} (θ : DirichletCharacter ℂ q)
    (hp : p.Prime) (τ : ℝ) :
    θ (p : ZMod q) * (p : ℂ) ^ (1 + I * (τ : ℂ)) =
      ((p : ℝ) / Real.log (p : ℝ)) •
        ((p : ℂ) ^ ((τ : ℂ) * I) *
          (θ (p : ZMod q) * (Real.log (p : ℝ) : ℂ))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlog : (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [Complex.cpow_add 1 (I * (τ : ℂ)) hp0, Complex.cpow_one, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_natCast, mul_comm I (τ : ℂ)]
  field_simp

lemma lemma56_actual_paper_prime_interval {D q : ℕ} (θ : DirichletCharacter ℂ q)
    (hP : 0 ≤ lemma23PaperP D) (τ : ℝ) :
    lemma56PrimeSum D θ τ =
      ∑ n ∈ Ico (⌊lemma23PaperP D⌋₊ + 1) ⌈lemma56PrimeUpper D⌉₊,
        if n.Prime then θ (n : ZMod q) * (n : ℂ) ^ (1 + I * (τ : ℂ)) else 0 := by
  unfold lemma56PrimeSum lemma56PaperPrimes
  rw [sum_filter]
  have hsub : Ico (⌊lemma23PaperP D⌋₊ + 1) ⌈lemma56PrimeUpper D⌉₊ ⊆
      range ⌈lemma56PrimeUpper D⌉₊ := by
    intro n hn
    exact mem_range.mpr (mem_Ico.mp hn).2
  rw [← sum_subset hsub]
  · apply sum_congr rfl
    intro n hn
    have hh := mem_Ico.mp hn
    have hlo : lemma23PaperP D < (n : ℝ) :=
      (Nat.floor_lt hP).mp (by omega)
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

end ZhangLS.Spec
