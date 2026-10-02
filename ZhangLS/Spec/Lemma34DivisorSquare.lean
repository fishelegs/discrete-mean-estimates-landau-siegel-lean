import ZhangLS.Spec.Lemma34Multichoose
import ZhangLS.Spec.Lemma34DivisorFunction
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

lemma lemma34_tau40_square_le_tau1600 (n : ℕ) :
    lemma34Tau 40 n ^ 2 ≤ lemma34Tau 1600 n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [lemma34Tau]
  · unfold lemma34Tau
    rw [(lemma34_tau_multiplicative 40).multiplicative_factorization _ hn,
      (lemma34_tau_multiplicative 1600).multiplicative_factorization _ hn]
    simp only [Finsupp.prod]
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod'
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    change lemma34Tau 40 (p ^ n.factorization p) ^ 2 ≤
      lemma34Tau 1600 (p ^ n.factorization p)
    rw [lemma34_tau_prime_power hp' 39,lemma34_tau_prime_power hp' 1599]
    exact lemma34_multichoose_40_square_le_1600 _

end ZhangLS.Spec
