import ZhangLS.Spec.Lemma83ModifiedEulerProduct
import ZhangLS.Spec.Lemma83LocalAgreement
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 300000

lemma lemma83_modified_local_excluded_hasSum (f : ArithmeticFunction ℂ) (d m : ℕ)
    (s : ℂ) (p : ℕ) (hpm : p ∣ m) :
    HasSum (lemma83ModifiedLocal f d m s p) (f (p^(d.factorization p))) := by
  convert hasSum_ite_eq 0 (f (p^(d.factorization p))) using 1
  funext e
  by_cases he : e = 0 <;> simp [lemma83ModifiedLocal,hpm,he]

lemma lemma83_modified_local_kappa_summable (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (d m : ℕ) (s : ℂ) (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    Summable (fun e => ‖lemma83ModifiedLocal (lemma83Kappa β) d m s p e‖) := by
  by_cases hpm : p ∣ m
  · exact summable_norm_iff.mpr (lemma83_modified_local_excluded_hasSum
      (lemma83Kappa β) d m s p hpm).summable
  · have ht : ‖(p:ℂ)^(-s)‖ < 1 := by
      rw [← lemma32_prime_monomial_eq_cpow hp.pos]
      exact lemma32_prime_monomial_norm_lt_one hp.one_lt s hs
    have hq (i : Fin 3) : ‖(p:ℂ)^(-β i)*(p:ℂ)^(-s)‖ < 1 := by
      simpa [norm_mul,lemma83_cpow_shift_norm hp.pos (β i) (hβ i)] using ht
    have hh := lemma83_local_kappa_shifted_summable ((p:ℂ)^(-β 0))
      ((p:ℂ)^(-β 1)) ((p:ℂ)^(-β 2)) ((p:ℂ)^(-s)) (d.factorization p)
      (hq 0) (hq 1) (hq 2)
    apply summable_norm_iff.mpr
    convert hh using 1
    funext e
    simp only [lemma83ModifiedLocal,hpm,false_and,if_false,lemma83_kappa_prime_power β hp]

lemma lemma83_modified_kappa_hasSum (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (d m : ℕ) (hd : d ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun h : Lemma83SupportedIndex d m => lemma83Kappa β (d*h.val)/(h.val:ℂ)^s)
      (∏ p ∈ d.primeFactors, ∑' e : ℕ, lemma83ModifiedLocal (lemma83Kappa β) d m s p e) :=
  lemma83_modified_supported_hasSum (lemma83Kappa β) (lemma83_kappa_multiplicative β)
    d m hd s (fun p hp => lemma83_modified_local_kappa_summable β hβ d m s hs
      (Nat.prime_of_mem_primeFactors hp))

lemma lemma83_modified_kappa_product (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (d m : ℕ) (hd : d ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    lemma83ModifiedKappa β d m s =
      ∏ p ∈ d.primeFactors,
        if p ∣ m then lemma83Kappa β (p^(d.factorization p)) else
          ∑' e : ℕ, lemma83Kappa β (p^(d.factorization p+e))*((p:ℂ)^(-s))^e := by
  rw [lemma83ModifiedKappa,(lemma83_modified_kappa_hasSum β hβ d m hd s hs).tsum_eq]
  apply prod_congr rfl
  intro p hp
  by_cases hpm : p ∣ m
  · rw [if_pos hpm,(lemma83_modified_local_excluded_hasSum (lemma83Kappa β) d m s p hpm).tsum_eq]
  · simp [lemma83ModifiedLocal,hpm]

end ZhangLS.Spec
