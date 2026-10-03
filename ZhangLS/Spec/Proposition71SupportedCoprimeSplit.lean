import ZhangLS.Spec.Lemma83SupportedFactored
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

/-- Positive integers coprime to the displayed modulus. -/
def Proposition71CoprimeIndex (m : ℕ) := {n : ℕ // n ≠ 0 ∧ n.Coprime m}

lemma proposition71_supported_coprime {d h r : ℕ}
    (hh : h ≠ 0) (hsub : h.primeFactors ⊆ d.primeFactors)
    (hr : r.Coprime d) : h.Coprime r := by
  apply Nat.coprime_of_dvd'
  intro p hp hph hpr
  have hpd := Nat.dvd_of_mem_primeFactors (hsub (Nat.mem_primeFactors.mpr ⟨hp,hph,hh⟩))
  exact False.elim (hp.ne_one (Nat.eq_one_of_dvd_coprimes hr hpr hpd))

/-- The smooth/rough decomposition uses actual prime factors and keeps every
prime shared by d and m excluded from the smooth part. -/
lemma proposition71_exists_supported_coprime_split {d m n : ℕ}
    (hd : d ≠ 0) (hn : n ≠ 0) (hnm : n.Coprime m) :
    ∃ h r : ℕ, h ≠ 0 ∧ h.primeFactors ⊆ d.primeFactors ∧ h.Coprime m ∧
      r ≠ 0 ∧ r.Coprime (d*m) ∧ h*r=n := by
  let h := (n.primeFactorsList.filter (fun p => p ∈ d.primeFactors)).prod
  let r := (n.primeFactorsList.filter (fun p => p ∉ d.primeFactors)).prod
  have hmem : h ∈ Nat.factoredNumbers d.primeFactors := Nat.prod_mem_factoredNumbers _ _
  have hhr : h*r=n := by
    have he := List.prod_map_filter_mul_prod_map_filter_not
      (fun p : ℕ => p ∈ d.primeFactors) (fun p : ℕ => p) n.primeFactorsList
    simpa only [List.map_id_fun', id_eq, Nat.prod_primeFactorsList hn] using he
  have hr0 : r ≠ 0 := by intro hz; rw [hz,mul_zero] at hhr; exact hn hhr.symm
  have hdiv : h ∣ n := ⟨r,hhr.symm⟩
  have rdiv : r ∣ n := ⟨h,by rw [mul_comm]; exact hhr.symm⟩
  have hrd : r.Coprime d := by
    apply Nat.coprime_of_dvd'
    intro p hp hpr hpd
    have hpin : p ∈ n.primeFactorsList.filter (fun p => p ∉ d.primeFactors) :=
      mem_list_primes_of_dvd_prod hp.prime
        (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hpr
    have hpnot : p ∉ d.primeFactors := by simpa only [decide_eq_true_eq] using List.of_mem_filter hpin
    exact False.elim (hpnot (Nat.mem_primeFactors.mpr ⟨hp,hpd,hd⟩))
  exact ⟨h,r,Nat.ne_zero_of_mem_factoredNumbers hmem,
    Nat.primeFactors_subset_of_mem_factoredNumbers hmem,
    Nat.Coprime.of_dvd_left hdiv hnm,hr0,
    hrd.mul_right (Nat.Coprime.of_dvd_left rdiv hnm),hhr⟩

lemma proposition71_supported_coprime_split_unique {d h₁ h₂ r₁ r₂ : ℕ}
    (hh₁ : h₁ ≠ 0) (hsub₁ : h₁.primeFactors ⊆ d.primeFactors)
    (hh₂ : h₂ ≠ 0) (hsub₂ : h₂.primeFactors ⊆ d.primeFactors)
    (hr₁ : r₁.Coprime d) (hr₂ : r₂.Coprime d)
    (he : h₁*r₁=h₂*r₂) : h₁=h₂ ∧ r₁=r₂ := by
  have hc₁ := proposition71_supported_coprime hh₁ hsub₁ hr₂
  have hc₂ := proposition71_supported_coprime hh₂ hsub₂ hr₁
  have hd₁ : h₁ ∣ h₂ := hc₁.dvd_of_dvd_mul_right (by rw [←he]; exact dvd_mul_right _ _)
  have hd₂ : h₂ ∣ h₁ := hc₂.dvd_of_dvd_mul_right (by rw [he]; exact dvd_mul_right _ _)
  have hh : h₁=h₂ := Nat.dvd_antisymm hd₁ hd₂
  refine ⟨hh,?_⟩
  rw [←hh] at he
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh₁) he

/-- Exact positive-index equivalence behind the factorization in source (7.19). -/
noncomputable def proposition71SupportedCoprimeEquiv (d m : ℕ) (hd : d ≠ 0) :
    Lemma83SupportedIndex d m × Proposition71CoprimeIndex (d*m) ≃
      Proposition71CoprimeIndex m :=
  Equiv.ofBijective (fun x => ⟨x.1.val*x.2.val,
    mul_ne_zero x.1.property.1 x.2.property.1,
    x.1.property.2.2.mul_left (x.2.property.2.of_dvd_right (dvd_mul_left m d))⟩) (by
    constructor
    · intro x y hxy
      have he : x.1.val*x.2.val=y.1.val*y.2.val := congrArg Subtype.val hxy
      have hu := proposition71_supported_coprime_split_unique
        x.1.property.1 x.1.property.2.1 y.1.property.1 y.1.property.2.1
        (x.2.property.2.of_dvd_right (dvd_mul_right d m))
        (y.2.property.2.of_dvd_right (dvd_mul_right d m)) he
      exact Prod.ext (Subtype.ext hu.1) (Subtype.ext hu.2)
    · intro n
      obtain ⟨h,r,hh,hs,hm,hr,hrm,he⟩ :=
        proposition71_exists_supported_coprime_split hd n.property.1 n.property.2
      exact ⟨(⟨h,hh,hs,hm⟩,⟨r,hr,hrm⟩),Subtype.ext he⟩)

lemma proposition71_supported_coprime_equiv_val (d m : ℕ) (hd : d ≠ 0)
    (x : Lemma83SupportedIndex d m × Proposition71CoprimeIndex (d*m)) :
    (proposition71SupportedCoprimeEquiv d m hd x).val=x.1.val*x.2.val := rfl

end ZhangLS.Spec
