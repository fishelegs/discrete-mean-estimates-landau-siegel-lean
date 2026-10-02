import ZhangLS.Spec.Lemma83Supported
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma83_supported_prime_power_eq {p m : ℕ} (hp : p.Prime) (e : ℕ)
    (h : Lemma83SupportedIndex (p^(e+1)) m) :
    h.val = p^(h.val.factorization p) := by
  apply Nat.eq_pow_of_factorization_eq_single h.property.1
  apply Finsupp.ext
  intro q
  by_cases hqp : q = p
  · subst q; simp
  have hq : q ∉ h.val.primeFactors := by
    intro hqh
    have hpp := h.property.2.1 hqh
    rw [Nat.primeFactors_pow p (Nat.succ_ne_zero e),hp.primeFactors] at hpp
    exact hqp (mem_singleton.mp hpp)
  have hz : h.val.factorization q = 0 := by
    rw [← Finsupp.notMem_support_iff,Nat.support_factorization]
    exact hq
  simp [hz,hqp]

/-- Prime powers are precisely the supported indices when q is not excluded. -/
noncomputable def lemma83SupportedPrimePowerEquiv {p m : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) (e : ℕ) : ℕ ≃ Lemma83SupportedIndex (p^(e+1)) m where
  toFun k := ⟨p^k,pow_ne_zero k hp.ne_zero,by
    intro q hq
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hp).mp
      ((Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))
    subst q
    rw [Nat.primeFactors_pow p (Nat.succ_ne_zero e),hp.primeFactors]
    simp,
    (hp.coprime_iff_not_dvd.mpr hpm).pow_left k⟩
  invFun h := h.val.factorization p
  left_inv k := by simp [hp.factorization_pow]
  right_inv h := by
    apply Subtype.ext
    exact (lemma83_supported_prime_power_eq hp e h).symm

/-- The exact supported infinite sum at a prime power, including every tail term. -/
lemma lemma83_modified_kappa_prime_power_unexcluded (β : Fin 3 → ℂ)
    {p m : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m) (e : ℕ) (s : ℂ) :
    lemma83ModifiedKappa β (p^(e+1)) m s =
      ∑' k : ℕ, lemma83Kappa β (p^(e+1+k)) * ((p : ℂ)^(-s))^k := by
  unfold lemma83ModifiedKappa
  rw [← (lemma83SupportedPrimePowerEquiv hp hpm e).tsum_eq]
  apply tsum_congr
  intro k
  simp only [lemma83SupportedPrimePowerEquiv,Equiv.coe_fn_mk]
  rw [← pow_add,Nat.cast_pow,← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul,div_eq_mul_inv,← inv_pow,Complex.cpow_neg]

end ZhangLS.Spec
