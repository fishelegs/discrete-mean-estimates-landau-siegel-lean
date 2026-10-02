import ZhangLS.Spec.Lemma83ModifiedKappaProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 400000

lemma lemma83_modified_kappa_mul (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b)
    (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    lemma83ModifiedKappa β (a*b) m s =
      lemma83ModifiedKappa β a m s * lemma83ModifiedKappa β b m s := by
  rw [lemma83_modified_kappa_product β hβ (a*b) m (mul_ne_zero ha hb) s hs,
    lemma83_modified_kappa_product β hβ a m ha s hs,
    lemma83_modified_kappa_product β hβ b m hb s hs,
    Nat.primeFactors_mul ha hb,prod_union hab.disjoint_primeFactors]
  congr 1
  · apply prod_congr rfl
    intro p hp
    have hpb : ¬p ∣ b := by
      intro h
      exact (Nat.prime_of_mem_primeFactors hp).ne_one
        (Nat.eq_one_of_dvd_coprimes hab (Nat.dvd_of_mem_primeFactors hp) h)
    simp [Nat.factorization_mul ha hb,Nat.factorization_eq_zero_of_not_dvd hpb]
  · apply prod_congr rfl
    intro p hp
    have hpa : ¬p ∣ a := by
      intro h
      exact (Nat.prime_of_mem_primeFactors hp).ne_one
        (Nat.eq_one_of_dvd_coprimes hab h (Nat.dvd_of_mem_primeFactors hp))
    simp [Nat.factorization_mul ha hb,Nat.factorization_eq_zero_of_not_dvd hpa]

/-- Adding factors coprime to the support does not change the supported sum. -/
lemma lemma83_modified_kappa_exclusion_invariant (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) {a k : ℕ} (ha : a ≠ 0) (hak : a.Coprime k)
    (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    lemma83ModifiedKappa β a (m*k) s = lemma83ModifiedKappa β a m s := by
  rw [lemma83_modified_kappa_product β hβ a (m*k) ha s hs,
    lemma83_modified_kappa_product β hβ a m ha s hs]
  apply prod_congr rfl
  intro p hp
  have hpk : ¬p ∣ k := by
    intro h
    exact (Nat.prime_of_mem_primeFactors hp).ne_one
      (Nat.eq_one_of_dvd_coprimes hak (Nat.dvd_of_mem_primeFactors hp) h)
  simp [(Nat.prime_of_mem_primeFactors hp).dvd_mul,hpk]

lemma lemma83_modified_lambda_mul (β : Fin 3 → ℂ) (j : Fin 3)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) (m : ℕ) :
    lemma83ModifiedLambda β j (a*b) m =
      lemma83ModifiedLambda β j a m * lemma83ModifiedLambda β j b m := by
  unfold lemma83ModifiedLambda
  rw [Nat.primeFactors_mul ha hb,filter_union,prod_union]
  exact hab.disjoint_primeFactors.mono (filter_subset _ _) (filter_subset _ _)

end ZhangLS.Spec
