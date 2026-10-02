import ZhangLS.Spec.Lemma83ModifiedEulerProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 300000

noncomputable def lemma152WeightedModifiedLocal (f w : ArithmeticFunction ℂ) (d m : ℕ)
    (s : ℂ) (p e : ℕ) : ℂ :=
  if p ∣ m ∧ e ≠ 0 then 0 else
    f (p^(d.factorization p+e))*w (p^e)*((p:ℂ)^(-s))^e

lemma lemma152_weighted_modified_local_product (f w : ArithmeticFunction ℂ) (hf : f.IsMultiplicative) (hw : w.IsMultiplicative)
    (d m : ℕ) (hd : d ≠ 0) (s : ℂ) (h : Nat.factoredNumbers d.primeFactors) :
    lemma83FactoredCoefficient d.primeFactors (lemma152WeightedModifiedLocal f w d m s) h.val =
      if h.val.Coprime m then f (d*h.val)*w h.val/(h.val:ℂ)^s else 0 := by
  have hh := (Nat.mem_factoredNumbers_iff_primeFactors_subset.mp h.property).1
  have hsub := (Nat.mem_factoredNumbers_iff_primeFactors_subset.mp h.property).2
  by_cases hc : h.val.Coprime m
  · rw [if_pos hc]
    have ht : f (d*h.val)*w h.val/(h.val:ℂ)^s =
        ∏ p ∈ d.primeFactors, f (p^(d.factorization p+h.val.factorization p))*
          w (p^(h.val.factorization p))*((p:ℂ)^(-s))^(h.val.factorization p) := by
      rw [show f (d*h.val)*w h.val/(h.val:ℂ)^s =
        (f (d*h.val)/(h.val:ℂ)^s)*w h.val by ring,
        lemma83_multiplicative_shifted_term_factorization f hf hd hh hsub s,
        lemma83_factorization_product_of_subset w hw hh d.primeFactors hsub,
        ← prod_mul_distrib]
      apply prod_congr rfl
      intro p hp
      ring
    rw [ht]
    unfold lemma83FactoredCoefficient
    apply prod_congr rfl
    intro p hp
    unfold lemma152WeightedModifiedLocal
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
    simp [lemma152WeightedModifiedLocal,hpm,(hp.factorization_pos_of_dvd hh hph).ne']

/-- Actual supported sums factor into local tails with the correct constant
coefficients. Local summability is the only analytic hypothesis. -/
lemma lemma152_weighted_modified_supported_hasSum (f w : ArithmeticFunction ℂ) (hf : f.IsMultiplicative) (hw : w.IsMultiplicative)
    (d m : ℕ) (hd : d ≠ 0) (s : ℂ)
    (hc : ∀ p ∈ d.primeFactors, Summable (fun e => ‖lemma152WeightedModifiedLocal f w d m s p e‖)) :
    HasSum (fun h : Lemma83SupportedIndex d m => f (d*h.val)*w h.val/(h.val:ℂ)^s)
      (∏ p ∈ d.primeFactors, ∑' e : ℕ, lemma152WeightedModifiedLocal f w d m s p e) := by
  have he := (lemma83_finite_supported_series d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (lemma152WeightedModifiedLocal f w d m s) hc).2
  have hi : HasSum
      ({h : Nat.factoredNumbers d.primeFactors | h.val.Coprime m}.indicator
        (fun h => f (d*h.val)*w h.val/(h.val:ℂ)^s))
      (∏ p ∈ d.primeFactors, ∑' e : ℕ, lemma152WeightedModifiedLocal f w d m s p e) := by
    convert he using 1
    funext h
    simp only [Set.indicator_apply,Set.mem_setOf_eq,lemma152_weighted_modified_local_product f w hf hw d m hd s h]
  have hs := hasSum_subtype_iff_indicator.mpr hi
  exact (lemma83SupportedSmoothEquiv d m).hasSum_iff.mpr hs

lemma lemma152_weighted_modified_supported_product (f w : ArithmeticFunction ℂ) (hf : f.IsMultiplicative) (hw : w.IsMultiplicative)
    (d m : ℕ) (hd : d ≠ 0) (s : ℂ)
    (hc : ∀ p ∈ d.primeFactors, Summable (fun e => ‖lemma152WeightedModifiedLocal f w d m s p e‖)) :
    (∑' h : Lemma83SupportedIndex d m, f (d*h.val)*w h.val/(h.val:ℂ)^s) =
      ∏ p ∈ d.primeFactors, ∑' e : ℕ, lemma152WeightedModifiedLocal f w d m s p e :=
  (lemma152_weighted_modified_supported_hasSum f w hf hw d m hd s hc).tsum_eq

end ZhangLS.Spec
