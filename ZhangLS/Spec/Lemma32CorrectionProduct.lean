import ZhangLS.Spec.Lemma32EulerLocalIdentity
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Nat
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_finite_ramification_prime_product {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) :
    (∏ p ∈ D.primeFactors.subtype Nat.Prime,
      (if p.val ∣ D then (1-lemma32PrimeMonomial p.val s)^4 else 1)) =
      lemma32RamificationFactor D s := by
  calc
    _ = ∏ p ∈ D.primeFactors.subtype Nat.Prime, (1-lemma32PrimeMonomial p.val s)^4 := by
      apply Finset.prod_congr rfl
      intro p hp
      have hd : p.val ∣ D := (Nat.mem_primeFactors.mp (Finset.mem_subtype.mp hp)).2.1
      rw [if_pos hd]
    _ = _ := by
      unfold lemma32RamificationFactor
      exact Finset.prod_subtype_of_mem (fun p : ℕ => (1-lemma32PrimeMonomial p s)^4)
        (fun p hp => Nat.prime_of_mem_primeFactors hp)

lemma lemma32_ramification_prime_factors_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) :
    HasProd (fun p : Nat.Primes => if p.val ∣ D then (1-lemma32PrimeMonomial p.val s)^4 else 1)
      (lemma32RamificationFactor D s) := by
  have hh : HasProd
      (fun p : Nat.Primes => if p.val ∣ D then (1-lemma32PrimeMonomial p.val s)^4 else 1)
      (∏ p ∈ D.primeFactors.subtype Nat.Prime,
        (if p.val ∣ D then (1-lemma32PrimeMonomial p.val s)^4 else 1)) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    have hn : ¬ p.val ∣ D := by
      intro hd
      apply hp
      exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.property,hd,χ.modulus_ne_zero⟩)
    rw [if_neg hn]
  rw [lemma32_finite_ramification_prime_product χ s] at hh
  exact hh

lemma lemma32_actual_local_corrections_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1/2 < s.re) :
    HasProd (fun p : Nat.Primes => lemma32LocalCorrection χ p.val (lemma32PrimeMonomial p.val s))
      (lemma32AnalyticCorrection χ s) := by
  have hf := lemma32_ramification_prime_factors_hasProd χ s
  have hr := (lemma32_regular_euler_product_multipliable χ s hs).hasProd
  have hh := hf.mul hr
  apply hh.congr_fun
  intro p
  exact (lemma32_actual_correction_regular_factorization χ p.property (lemma32PrimeMonomial p.val s)
    (lemma32_prime_monomial_norm_lt_one p.property.one_lt s (by linarith)))

end ZhangLS.Spec
