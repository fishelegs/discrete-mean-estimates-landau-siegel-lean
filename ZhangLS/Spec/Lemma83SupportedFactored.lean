import ZhangLS.Spec.Lemma83Supported
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 200000

lemma lemma83_supported_iff_factored (d m h : ℕ) :
    (h ≠ 0 ∧ h.primeFactors ⊆ d.primeFactors ∧ h.Coprime m) ↔
      h ∈ Nat.factoredNumbers (d.primeFactors.filter (fun p => ¬p ∣ m)) := by
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  constructor
  · rintro ⟨hh,hd,hcop⟩
    refine ⟨hh,?_⟩
    intro p hp
    apply mem_filter.mpr
    refine ⟨hd hp,?_⟩
    intro hpm
    exact (Nat.prime_of_mem_primeFactors hp).ne_one
      (Nat.eq_one_of_dvd_coprimes hcop (Nat.dvd_of_mem_primeFactors hp) hpm)
  · rintro ⟨hh,hs⟩
    refine ⟨hh,fun p hp => (mem_filter.mp (hs hp)).1,?_⟩
    apply Nat.coprime_of_dvd'
    intro p hp hph hpm
    exact False.elim ((mem_filter.mp (hs (Nat.mem_primeFactors.mpr ⟨hp,hph,hh⟩))).2 hpm)

noncomputable def lemma83SupportedFactoredEquiv (d m : ℕ) :
    Lemma83SupportedIndex d m ≃ Nat.factoredNumbers (d.primeFactors.filter (fun p => ¬p ∣ m)) where
  toFun h := ⟨h.val,(lemma83_supported_iff_factored d m h.val).mp h.property⟩
  invFun h := ⟨h.val,(lemma83_supported_iff_factored d m h.val).mpr h.property⟩
  left_inv h := rfl
  right_inv h := rfl

lemma lemma83_modified_kappa_factored (β : Fin 3 → ℂ) (d m : ℕ) (s : ℂ) :
    lemma83ModifiedKappa β d m s =
      ∑' h : Nat.factoredNumbers (d.primeFactors.filter (fun p => ¬p ∣ m)),
        lemma83Kappa β (d*h.val)/(h.val:ℂ)^s := by
  unfold lemma83ModifiedKappa
  exact (lemma83SupportedFactoredEquiv d m).tsum_eq
    (fun h : Nat.factoredNumbers (d.primeFactors.filter (fun p => ¬p ∣ m)) =>
      lemma83Kappa β (d*h.val)/(h.val:ℂ)^s)

end ZhangLS.Spec
