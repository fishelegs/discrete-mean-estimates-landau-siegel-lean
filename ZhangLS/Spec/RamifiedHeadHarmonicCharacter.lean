import ZhangLS.Spec.Lemma36CoefficientMajorant
import ZhangLS.Spec.Lemma34TauProduct

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma ramifiedHead_nu_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (hpD : p ∣ D) (e : ℕ) :
    lemma23NuArithmeticFunction χ (p^e) = 1 := by
  rw [lemma31_actual_nu_prime_power χ hp,
    χ.evalNat_eq_zero_of_dvd_modulus hpD hp.ne_one]
  simp

/-- Multiplying by any divisor of the conductor leaves the actual ν unchanged,
including when the multiplier and argument share ramified primes. -/
theorem ramifiedHead_nu_mul_divisor {D q n : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : D ≠ 0) (hq : q ∣ D) :
    lemma23NuArithmeticFunction χ (q*n) = lemma23NuArithmeticFunction χ n := by
  by_cases hn : n = 0
  · subst n; simp
  have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero hD hq
  let f := lemma23NuArithmeticFunction χ
  have hf : f.IsMultiplicative := lemma31_actual_nu_multiplicative χ
  have hf0 : ∀ {p : ℕ}, f (p^0) = 1 := by intro p; simp [hf.map_one]
  change f (q*n) = f n
  rw [hf.multiplicative_factorization f (Nat.mul_ne_zero hq0 hn),
    hf.multiplicative_factorization f hn]
  rw [Finsupp.prod_of_support_subset _ _ _ (fun _ _ => hf0)
      (s := q.primeFactors ∪ n.primeFactors),
    Finsupp.prod_of_support_subset _ _ _ (fun _ _ => hf0)
      (s := q.primeFactors ∪ n.primeFactors)]
  · apply prod_congr rfl
    intro p hp
    have hpp : p.Prime := by
      rcases mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    by_cases hpq : p ∣ q
    · have hpD := dvd_trans hpq hq
      exact (ramifiedHead_nu_prime_power χ hpp hpD _).trans
        (ramifiedHead_nu_prime_power χ hpp hpD _).symm
    · rw [Nat.factorization_mul hq0 hn, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpq, zero_add]
  · exact subset_union_right
  · simpa [Nat.primeFactors_mul hq0 hn]

end ZhangLS.Spec
