import ZhangLS.Spec.Lemma83Definitions

/-! # Exact finite arithmetic factors in Proposition 7.1

These identities use the genuine supported κ̃ and ξ defined in Section 7.
There are no model coefficients or assumed Euler-product identities.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- The prime support of mn is the disjoint union of the support of m and
those primes of n not dividing m. Repeated prime factors are counted once. -/
theorem proposition71_prime_support_union {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m*n).primeFactors = m.primeFactors ∪ n.primeFactors.filter (fun q => ¬q ∣ m) := by
  rw [Nat.primeFactors_mul hm hn]
  ext q
  simp only [mem_union,mem_filter]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · by_cases hqm : q ∣ m
      · exact Or.inl (Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors h,hqm,hm⟩)
      · exact Or.inr ⟨h,hqm⟩
  · intro h
    exact h.elim Or.inl (fun h => Or.inr h.1)

/-- Exactly λ₀ⱼ(mn)=λ₀ⱼ(m) λ̃₀ⱼ(n,m), without a coprimality hypothesis. -/
theorem proposition71_lambda_factorization (β : Fin 3 → ℂ) (j : Fin 3)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    lemma83Lambda β (m*n) (1-β j) =
      lemma83Lambda β m (1-β j) * lemma83ModifiedLambda β j n m := by
  have hd : Disjoint m.primeFactors (n.primeFactors.filter (fun q => ¬q ∣ m)) := by
    rw [disjoint_left]
    intro q hqm hqn
    exact (mem_filter.mp hqn).2 (Nat.dvd_of_mem_primeFactors hqm)
  unfold lemma83Lambda lemma83ModifiedLambda
  rw [proposition71_prime_support_union hm hn,prod_union hd]

/-- The final coefficient factorization immediately before (7.21). -/
theorem proposition71_xi_factor_extraction (β : Fin 3 → ℂ) (j : Fin 3)
    {n d r : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) (hr : r ≠ 0) :
    lemma83Lambda β (d*r*n) (1-β j) *
      (∑ a ∈ n.divisorsAntidiagonal.filter (fun a => a.2.Coprime r),
        lemma83ModifiedKappa β a.1 (d*r*a.2) (1-β j) *
          (ArithmeticFunction.moebius a.2 : ℂ) * (a.2 : ℂ)^(1-β j) /
            (Nat.totient a.2 : ℂ)) =
    lemma83Lambda β (d*r) (1-β j) * lemma83Xi β j n d r := by
  rw [proposition71_lambda_factorization β j (Nat.mul_ne_zero hd hr) hn]
  unfold lemma83Xi
  ring

end ZhangLS.Spec
