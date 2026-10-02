import ZhangLS.Spec.Lemma162PrimeSupportedConvolution
import ZhangLS.Spec.Lemma161DirichletSeries

/-! Reindex an explicitly prime-supported
L-series without assuming multiplicativity or a unit coefficient at one. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma162_arithmetic_prime_power_term (f : ArithmeticFunction ℂ)
    {p : ℕ} (hp : 0<p) (s : ℂ) (r : ℕ) :
    LSeries.term f s (p^r) = f (p^r)*lemma32PrimeMonomial p s^r := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero r hp.ne'),Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul p r s,Complex.cpow_nat_mul,
    div_eq_mul_inv,← inv_pow,← Complex.cpow_neg,← lemma32_prime_monomial_eq_cpow hp s]

lemma lemma162_prime_supported_term_zero (p : ℕ) (f : ArithmeticFunction ℂ)
    (s : ℂ) (n : ℕ) (hn : n ∉ Set.range (fun r : ℕ => p^r)) :
    LSeries.term (lemma162PrimePowerPart p f) s n = 0 := by
  have hn' : ¬ ∃ r : ℕ, n=p^r := by
    rintro ⟨r,hr⟩
    exact hn ⟨r,hr.symm⟩
  simp [LSeries.term,lemma162PrimePowerPart,hn']

lemma lemma162_prime_supported_lseries_hasSum {p : ℕ} (hp : p.Prime)
    (f : ArithmeticFunction ℂ) (s Z : ℂ)
    (hsum : HasSum (fun r : ℕ => f (p^r)*lemma32PrimeMonomial p s^r) Z) :
    LSeriesHasSum (lemma162PrimePowerPart p f) s Z := by
  change HasSum (LSeries.term (lemma162PrimePowerPart p f) s) Z
  apply ((Nat.pow_right_injective hp.two_le).hasSum_iff
    (lemma162_prime_supported_term_zero p f s)).mp
  convert hsum using 1
  funext r
  simp only [Function.comp_apply,lemma162_arithmetic_prime_power_term _ hp.pos,
    lemma162_prime_power_part_apply]

lemma lemma162_prime_supported_lseries_summable {p : ℕ} (hp : p.Prime)
    (f : ArithmeticFunction ℂ) (s : ℂ)
    (hsum : Summable (fun r : ℕ => f (p^r)*lemma32PrimeMonomial p s^r)) :
    LSeriesSummable (lemma162PrimePowerPart p f) s := by
  exact (lemma162_prime_supported_lseries_hasSum hp f s _ hsum.hasSum).LSeriesSummable

lemma lemma162_prime_supported_lseries_eq {p : ℕ} (hp : p.Prime)
    (f : ArithmeticFunction ℂ) (s Z : ℂ)
    (hsum : HasSum (fun r : ℕ => f (p^r)*lemma32PrimeMonomial p s^r) Z) :
    LSeries (lemma162PrimePowerPart p f) s = Z :=
  (lemma162_prime_supported_lseries_hasSum hp f s Z hsum).LSeries_eq

/-- Support restriction commutes with pointwise weighting; this permits
reindexing the actual weighted 2-adic part using the preceding lemmas. -/
lemma lemma162_prime_power_part_pmul (p : ℕ) (f h : ArithmeticFunction ℂ) :
    (lemma162PrimePowerPart p f).pmul h = lemma162PrimePowerPart p (f.pmul h) := by
  ext n
  simp only [ArithmeticFunction.pmul_apply,lemma162PrimePowerPart,ArithmeticFunction.coe_mk]
  split_ifs <;> simp

end ZhangLS.Spec
