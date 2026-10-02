import ZhangLS.Spec.Lemma56ActualPrimeMassNormalization

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Finset Filter
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      (1 / 2 : ℝ) * lemma23PaperP D / lemma23PaperL D ^ 68 ≤
        ∑ p ∈ (Finset.range ⌈lemma56PrimeUpper D⌉₊).filter
          (fun p : ℕ => p.Prime ∧ lemma23PaperP D < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) < lemma56PrimeUpper D),
            Real.log ((p : ℕ) : ℝ) := by
  simpa only [lemma56PaperPrimeLogMass, lemma56PaperPrimes] using
    lemma56_uniform_actual_prime_log_mass_lower

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      (1 / 4 : ℝ) * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 ≤
        ∑ p ∈ (Finset.range ⌈lemma56PrimeUpper D⌉₊).filter
          (fun p : ℕ => p.Prime ∧ lemma23PaperP D < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) < lemma56PrimeUpper D), ((p : ℕ) : ℝ) := by
  simpa only [lemma56PrimeMass, lemma56PaperPrimes] using lemma56_uniform_actual_prime_mass_lower

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
    (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ τ : ℝ, |τ| ≤ D →
      ‖∑ p ∈ lemma56PaperPrimes D, θ (p : ZMod q) * (p : ℂ) ^ (1 + I * (τ : ℂ))‖ ≤
        C * (∑ p ∈ lemma56PaperPrimes D, ((p : ℕ) : ℝ)) *
          Real.exp (-(lemma23PaperL D ^ (9 / 2 : ℝ))) := by
  simpa only [lemma56PrimeSum, lemma56PrimeMass, lemma56Decay] using
    lemma56_uniform_primitive_prime_window_normalized_bound

example {D : ℕ} (hL : 10000000 ≤ lemma23PaperL D) :
    ((∑ p ∈ lemma56PaperPrimes D, Real.log ((p : ℕ) : ℝ)) : ℂ) =
      (∑ n ∈ Finset.range ⌈lemma56PrimeUpper D⌉₊, if n.Prime then (Real.log (n : ℝ) : ℂ) else 0) -
        (∑ n ∈ Finset.range (⌊lemma23PaperP D⌋₊ + 1), if n.Prime then (Real.log (n : ℝ) : ℂ) else 0) := by
  simpa only [lemma56PaperPrimeLogMass, Complex.ofReal_sum, lemma56SharpPrimeLogSum,
    lemma56PaperPrimeLowerCut, Nat.ceil_natCast, ofReal_zero, zero_mul, Complex.cpow_zero,
    lemma56_principal_one_apply_nat, one_mul] using lemma56_actual_prime_log_mass_prefix_difference hL

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      0 < ‖∑ p ∈ lemma56PaperPrimes D, (p : ℂ)‖ := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_actual_prime_mass_pos
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA
  have hn : ‖∑ p ∈ lemma56PaperPrimes D, (p : ℂ)‖ = lemma56PrimeMass D := by
    simpa only [lemma56PrimeSum, ofReal_zero, mul_zero, add_zero, Complex.cpow_one,
      lemma56_principal_one_apply_nat, one_mul] using lemma56_principal_paper_sum_zero_height D
  rw [hn]
  exact h χ hDN hD hA

example {D n : ℕ} (hn : (n : ℝ) = lemma23PaperP D ∨ (n : ℝ) = lemma56PrimeUpper D) :
    n ∉ lemma56PaperPrimes D := by
  intro hm
  have hh := (lemma56_mem_paper_primes D n).mp hm
  rcases hn with hl | hu
  · rw [hl] at hh
    exact (lt_irrefl _) hh.2.1
  · rw [hu] at hh
    exact (lt_irrefl _) hh.2.2

#print axioms lemma56_principal_mass_window_width
#print axioms lemma56_principal_mass_prefix_error_budget
#print axioms lemma56_paper_prime_mass_cut_parameters
#print axioms lemma56_actual_paper_prime_log_interval
#print axioms lemma56_actual_prime_log_mass_prefix_difference
#print axioms lemma56_principal_mass_main_factor_ge_one
#print axioms lemma56_actual_prime_log_mass_main_error_of_prefix
#print axioms lemma56_actual_prime_log_mass_lower_of_main_error
#print axioms lemma56_uniform_actual_prime_mass_threshold
#print axioms lemma56_uniform_actual_prime_log_mass_lower
#print axioms lemma56_uniform_actual_prime_mass_lower
#print axioms lemma56_uniform_primitive_prime_window_normalized_bound
#print axioms lemma56_uniform_actual_prime_mass_pos
#print axioms lemma56_uniform_actual_prime_window_nonempty

end ZhangLS.Spec
