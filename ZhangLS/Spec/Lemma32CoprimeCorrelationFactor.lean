import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical

lemma lemma32_coprime_gcd_product {m n δ : ℕ} (h : m.Coprime n) :
    (m*n).gcd δ = m.gcd δ * n.gcd δ := by
  apply Nat.dvd_antisymm
  · simpa only [gcd_eq_nat_gcd, Nat.gcd_comm] using (gcd_mul_dvd_mul_gcd δ m n)
  · apply Nat.dvd_gcd
    · exact Nat.mul_dvd_mul (Nat.gcd_dvd_left m δ) (Nat.gcd_dvd_left n δ)
    · have hc : (m.gcd δ).Coprime (n.gcd δ) := by
        simpa only [Nat.gcd_comm] using h.gcd_both δ δ
      exact hc.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right m δ) (Nat.gcd_dvd_right n δ)

noncomputable def lemma32SquarefreeCorrelationFactor (m δ : ℕ) : ℝ :=
  (3 : ℝ)^m.primeFactors.card * Real.sqrt (m : ℝ) * Real.sqrt (m.gcd δ : ℝ)

lemma lemma32_coprime_correlation_factor_mul {m n δ : ℕ} (h : m.Coprime n) :
    lemma32SquarefreeCorrelationFactor (m*n) δ =
      lemma32SquarefreeCorrelationFactor m δ * lemma32SquarefreeCorrelationFactor n δ := by
  unfold lemma32SquarefreeCorrelationFactor
  rw [h.primeFactors_mul, Finset.card_union_of_disjoint h.disjoint_primeFactors,
    pow_add, Nat.cast_mul, lemma32_coprime_gcd_product h, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_mul (Nat.cast_nonneg (m.gcd δ))]
  ring

lemma lemma32_prime_correlation_factor {p δ : ℕ} (hp : p.Prime) :
    lemma32SquarefreeCorrelationFactor p δ =
      3 * Real.sqrt (p : ℝ) * Real.sqrt (p.gcd δ : ℝ) := by
  simp [lemma32SquarefreeCorrelationFactor, hp.primeFactors]

lemma lemma32_correlation_factor_one (δ : ℕ) :
    lemma32SquarefreeCorrelationFactor 1 δ = 1 := by
  simp [lemma32SquarefreeCorrelationFactor]

end ZhangLS.Spec
