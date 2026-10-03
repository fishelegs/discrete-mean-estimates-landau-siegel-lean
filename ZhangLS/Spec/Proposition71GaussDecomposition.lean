import ZhangLS.Spec.Proposition71Support

/-! # Exact principal correction and long-nonunit restoration term

For a genuine short unit k, the normalized primitive Gauss average is exactly
an additive character plus (1−e)/p minus the l=0 branch. This formula keeps the
nonunit correction explicit and does not hide it in totalized division.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2500000

lemma proposition71_additive_character_norm {p : ℕ} [NeZero p] (l k : ZMod p) :
    ‖ZMod.stdAddChar (l*k⁻¹)‖=1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma proposition71_additive_character_correction_norm {p : ℕ} [NeZero p] (l k : ZMod p) :
    ‖1-ZMod.stdAddChar (l*k⁻¹)‖≤2 := by
  exact (norm_sub_le (1 : ℂ) _).trans_eq (by rw [norm_one,proposition71_additive_character_norm]; norm_num)

/-- The exact nonunit-restored identity, valid also at l=0. -/
theorem proposition71_normalized_gauss_decomposition {p : ℕ} [NeZero p]
    (hp : p.Prime) (l k : ZMod p) (hk : IsUnit k) :
    (∑ψ∈(univ : Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum ψ⁻¹ ZMod.stdAddChar*ψ l*ψ⁻¹ k)/(p : ℂ)=
      ZMod.stdAddChar (l*k⁻¹)+(p : ℂ)⁻¹*(1-ZMod.stdAddChar (l*k⁻¹))-
        if l=0 then 1 else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hl : l=0
  · subst l
    rw [proposition71_gauss_average_nonunit 0 k (Or.inl not_isUnit_zero)]
    simp
  · have hlu : IsUnit l := isUnit_iff_ne_zero.mpr hl
    rw [proposition71_primitive_gauss_average hp l k hlu hk,if_neg hl,sub_zero]
    have hφ : (p.totient : ℂ)=(p : ℂ)-1 := by
      rw [Nat.totient_prime hp,Nat.cast_sub hp.one_le]
      simp
    rw [hφ]
    have hpc : (p : ℂ)≠0 := by exact_mod_cast hp.ne_zero
    field_simp
    ring

/-- Natural-index form: the extra term is exactly the p-divisible long branch. -/
theorem proposition71_normalized_gauss_nat_decomposition {D p n : ℕ} [NeZero p]
    (hp : p∈lemma56PaperPrimes D) (hn : n∈lemma81PolynomialIndices D) (m : ℕ) :
    (∑ψ∈(univ : Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum ψ⁻¹ ZMod.stdAddChar*ψ (m : ZMod p)*ψ⁻¹ (n : ZMod p))/(p : ℂ)=
      ZMod.stdAddChar ((m : ZMod p)*(n : ZMod p)⁻¹)+
        (p : ℂ)⁻¹*(1-ZMod.stdAddChar ((m : ZMod p)*(n : ZMod p)⁻¹))-
        if p∣m then 1 else 0 := by
  have hs := (proposition71_mem_indices D n).mp hn
  have hu := proposition71_short_index_unit hp hs.1 hs.2
  rw [proposition71_normalized_gauss_decomposition ((lemma56_mem_paper_primes D p).mp hp).1 _ _ hu]
  simp only [ZMod.natCast_eq_zero_iff m p]

end ZhangLS.Spec
