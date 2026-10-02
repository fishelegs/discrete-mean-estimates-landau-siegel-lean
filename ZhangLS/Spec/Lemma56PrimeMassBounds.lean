import ZhangLS.Spec.Lemma56PrimeWindowAbsolute


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PaperPrimeLogMass (D : ℕ) : ℝ :=
  ∑ p ∈ lemma56PaperPrimes D, Real.log (p : ℝ)

lemma lemma56_paper_prime_log_mass_nonneg (D : ℕ) : 0 ≤ lemma56PaperPrimeLogMass D := by
  apply sum_nonneg
  intro p hp
  have hh := (lemma56_mem_paper_primes D p).mp hp
  exact Real.log_nonneg (by exact_mod_cast hh.1.one_lt.le)

lemma lemma56_actual_prime_mass_card_bounds (D : ℕ) :
    lemma23PaperP D * (lemma56PaperPrimes D).card ≤ lemma56PrimeMass D ∧
      lemma56PrimeMass D ≤ lemma56PrimeUpper D * (lemma56PaperPrimes D).card := by
  constructor
  · have hh : (∑ p ∈ lemma56PaperPrimes D, lemma23PaperP D) ≤
        ∑ p ∈ lemma56PaperPrimes D, (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact ((lemma56_mem_paper_primes D p).mp hp).2.1.le
    simpa only [sum_const, nsmul_eq_mul, mul_comm, lemma56PrimeMass] using hh
  · have hh : (∑ p ∈ lemma56PaperPrimes D, (p : ℝ)) ≤
        ∑ p ∈ lemma56PaperPrimes D, lemma56PrimeUpper D := by
      apply sum_le_sum
      intro p hp
      exact ((lemma56_mem_paper_primes D p).mp hp).2.2.le
    simpa only [sum_const, nsmul_eq_mul, mul_comm, lemma56PrimeMass] using hh

lemma lemma56_actual_prime_mass_from_logmass {D : ℕ}
    (hY : 1 < lemma56PrimeUpper D) :
    (lemma23PaperP D / Real.log (lemma56PrimeUpper D)) *
      lemma56PaperPrimeLogMass D ≤ lemma56PrimeMass D := by
  have hlogY : 0 < Real.log (lemma56PrimeUpper D) := Real.log_pos hY
  have hP : 0 ≤ lemma23PaperP D := (Real.exp_pos _).le
  calc
    _ = ∑ p ∈ lemma56PaperPrimes D,
        (lemma23PaperP D / Real.log (lemma56PrimeUpper D)) * Real.log (p : ℝ) := by
      rw [lemma56PaperPrimeLogMass, mul_sum]
    _ ≤ lemma56PrimeMass D := by
      apply sum_le_sum
      intro p hp
      have hh := (lemma56_mem_paper_primes D p).mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hh.1.one_lt.le)
      have hl := Real.log_le_log hp0 hh.2.2.le
      have h1 := mul_le_mul_of_nonneg_right hh.2.1.le hlogp
      have h2 := mul_le_mul_of_nonneg_left hl hp0.le
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hlogY).mpr (h1.trans h2)

end ZhangLS.Spec
