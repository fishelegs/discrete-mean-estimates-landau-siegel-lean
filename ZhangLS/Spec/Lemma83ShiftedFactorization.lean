import ZhangLS.Spec.Lemma83SupportedFactored
import ZhangLS.Spec.Lemma83KappaPrimePower
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 300000

lemma lemma83_factorization_product (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    {n : ℕ} (hn : n ≠ 0) :
    f n = ∏ p ∈ n.primeFactors, f (p^(n.factorization p)) := by
  rw [hf.multiplicative_factorization f hn,Nat.prod_factorization_eq_prod_primeFactors]

lemma lemma83_factorization_product_of_subset (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {h : ℕ} (hh : h ≠ 0) (S : Finset ℕ)
    (hS : h.primeFactors ⊆ S) :
    f h = ∏ p ∈ S, f (p^(h.factorization p)) := by
  rw [lemma83_factorization_product f hf hh]
  apply prod_subset hS
  intro p hp hph
  have he : h.factorization p = 0 := by
    rwa [← Finsupp.notMem_support_iff,Nat.support_factorization]
  rw [he,pow_zero,hf.map_one]

/-- A multiplicative coefficient times h⁻ˢ factors without dividing by f(d). -/
lemma lemma83_multiplicative_shifted_term_factorization (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {d h : ℕ} (hd : d ≠ 0) (hh : h ≠ 0)
    (hsub : h.primeFactors ⊆ d.primeFactors) (s : ℂ) :
    f (d*h)/(h:ℂ)^s = ∏ p ∈ d.primeFactors,
      f (p^(d.factorization p+h.factorization p))*((p:ℂ)^(-s))^(h.factorization p) := by
  have hdh : (d*h).primeFactors = d.primeFactors := by
    rw [Nat.primeFactors_mul hd hh,union_eq_left.mpr hsub]
  have hfac := lemma83_factorization_product f hf (mul_ne_zero hd hh)
  rw [hdh,Nat.factorization_mul hd hh] at hfac
  simp only [Finsupp.coe_add,Pi.add_apply] at hfac
  have hw := lemma83_factorization_product_of_subset (lemma83PowerCoefficient s)
    (lemma83_power_coefficient_multiplicative s) hh d.primeFactors hsub
  have hw' : (h:ℂ)^(-s) =
      ∏ p ∈ d.primeFactors, ((p:ℂ)^(-s))^(h.factorization p) := by
    simpa only [lemma83PowerCoefficient,ArithmeticFunction.coe_mk,if_neg hh] using
      hw.trans (prod_congr rfl (fun p hp => lemma83_power_coefficient_prime_power s
        (Nat.prime_of_mem_primeFactors hp) (h.factorization p)))
  rw [div_eq_mul_inv,← Complex.cpow_neg,hfac,hw',← prod_mul_distrib]

end ZhangLS.Spec
