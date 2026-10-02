import ZhangLS.Spec.Lemma83FiniteSupportedSeries
import ZhangLS.Spec.Lemma83ShiftedFactorization
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 300000

noncomputable def lemma83ModifiedLocal (f : ArithmeticFunction ℂ) (d m : ℕ)
    (s : ℂ) (p e : ℕ) : ℂ :=
  if p ∣ m ∧ e ≠ 0 then 0 else
    f (p^(d.factorization p+e))*((p:ℂ)^(-s))^e

noncomputable def lemma83SupportedSmoothEquiv (d m : ℕ) :
    Lemma83SupportedIndex d m ≃
      {h : Nat.factoredNumbers d.primeFactors // h.val.Coprime m} where
  toFun h := ⟨⟨h.val,Nat.mem_factoredNumbers_iff_primeFactors_subset.mpr
    ⟨h.property.1,h.property.2.1⟩⟩,h.property.2.2⟩
  invFun h := ⟨h.val.val,(Nat.mem_factoredNumbers_iff_primeFactors_subset.mp h.val.property).1,
    (Nat.mem_factoredNumbers_iff_primeFactors_subset.mp h.val.property).2,h.property⟩
  left_inv h := rfl
  right_inv h := rfl

lemma lemma83_modified_local_product (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (d m : ℕ) (hd : d ≠ 0) (s : ℂ) (h : Nat.factoredNumbers d.primeFactors) :
    lemma83FactoredCoefficient d.primeFactors (lemma83ModifiedLocal f d m s) h.val =
      if h.val.Coprime m then f (d*h.val)/(h.val:ℂ)^s else 0 := by
  have hh := (Nat.mem_factoredNumbers_iff_primeFactors_subset.mp h.property).1
  have hsub := (Nat.mem_factoredNumbers_iff_primeFactors_subset.mp h.property).2
  by_cases hc : h.val.Coprime m
  · rw [if_pos hc,lemma83_multiplicative_shifted_term_factorization f hf hd hh hsub s]
    unfold lemma83FactoredCoefficient
    apply prod_congr rfl
    intro p hp
    unfold lemma83ModifiedLocal
    apply if_neg
    rintro ⟨hpm,he⟩
    have hph : p ∈ h.val.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr he
    exact (Nat.prime_of_mem_primeFactors hp).ne_one
      (Nat.eq_one_of_dvd_coprimes hc (Nat.dvd_of_mem_primeFactors hph) hpm)
  · rw [if_neg hc]
    obtain ⟨p,hp,hph,hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hps : p ∈ d.primeFactors := hsub (Nat.mem_primeFactors.mpr ⟨hp,hph,hh⟩)
    unfold lemma83FactoredCoefficient
    apply prod_eq_zero hps
    simp [lemma83ModifiedLocal,hpm,(hp.factorization_pos_of_dvd hh hph).ne']

/-- Actual supported sums factor into local tails with the correct constant
coefficients. Local summability is the only analytic hypothesis. -/
lemma lemma83_modified_supported_hasSum (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (d m : ℕ) (hd : d ≠ 0) (s : ℂ)
    (hc : ∀ p ∈ d.primeFactors, Summable (fun e => ‖lemma83ModifiedLocal f d m s p e‖)) :
    HasSum (fun h : Lemma83SupportedIndex d m => f (d*h.val)/(h.val:ℂ)^s)
      (∏ p ∈ d.primeFactors, ∑' e : ℕ, lemma83ModifiedLocal f d m s p e) := by
  have he := (lemma83_finite_supported_series d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (lemma83ModifiedLocal f d m s) hc).2
  have hi : HasSum
      ({h : Nat.factoredNumbers d.primeFactors | h.val.Coprime m}.indicator
        (fun h => f (d*h.val)/(h.val:ℂ)^s))
      (∏ p ∈ d.primeFactors, ∑' e : ℕ, lemma83ModifiedLocal f d m s p e) := by
    convert he using 1
    funext h
    simp only [Set.indicator_apply,Set.mem_setOf_eq,lemma83_modified_local_product f hf d m hd s h]
  have hs := hasSum_subtype_iff_indicator.mpr hi
  exact (lemma83SupportedSmoothEquiv d m).hasSum_iff.mpr hs

lemma lemma83_modified_supported_product (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (d m : ℕ) (hd : d ≠ 0) (s : ℂ)
    (hc : ∀ p ∈ d.primeFactors, Summable (fun e => ‖lemma83ModifiedLocal f d m s p e‖)) :
    (∑' h : Lemma83SupportedIndex d m, f (d*h.val)/(h.val:ℂ)^s) =
      ∏ p ∈ d.primeFactors, ∑' e : ℕ, lemma83ModifiedLocal f d m s p e :=
  (lemma83_modified_supported_hasSum f hf d m hd s hc).tsum_eq

end ZhangLS.Spec
