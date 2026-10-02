import ZhangLS.Spec.Lemma33GaussTransform

/-! # Exact primitive-prime Gauss averaging in (7.7)

The actual average is (p-1)e(l/k)+1. Its difference from the printed
p e(l/k) has norm at most two, independently of p,l,k. No cancellation
estimate is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_prime_primitive_iff {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ : DirichletCharacter ℂ p) : ψ.IsPrimitive ↔ ψ ≠ 1 := by
  constructor
  · exact lemma33_primitive_nonprincipal hp ψ
  · intro h
    rcases (Nat.dvd_prime hp).mp ψ.conductor_dvd_level with hc | hc
    · exact (h (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc)).elim
    · exact hc

/-- Character orthogonality gives the exact full Gauss average. -/
theorem proposition71_full_gauss_average {p : ℕ} [NeZero p] (hp : p.Prime)
    (l k : ZMod p) (hl : IsUnit l) (hk : IsUnit k) :
    (∑ ψ : DirichletCharacter ℂ p,
      gaussSum ψ⁻¹ ZMod.stdAddChar * ψ l * ψ⁻¹ k) =
      (p.totient : ℂ) * ZMod.stdAddChar (l * k⁻¹) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk0 : k ≠ 0 := hk.ne_zero
  have horth (a : ZMod p) :
      (∑ ψ : DirichletCharacter ℂ p, ψ⁻¹ a * ψ l * ψ⁻¹ k) =
        if a = l * k⁻¹ then (p.totient : ℂ) else 0 := by
    have hc : (∑ ψ : DirichletCharacter ℂ p, ψ⁻¹ a * ψ l * ψ⁻¹ k) =
        ∑ ψ : DirichletCharacter ℂ p, ψ l * star (ψ (a*k)) := by
      apply sum_congr rfl
      intro ψ hψ
      rw [MulChar.star_apply',map_mul]
      ring
    rw [hc,lemma23_dirichletCharacter_hermitian_orthogonality hl]
    congr 1
    exact propext (by rw [eq_comm,← eq_div_iff hk0,div_eq_mul_inv])
  calc
    _ = ∑ a : ZMod p, ZMod.stdAddChar a *
        ∑ ψ : DirichletCharacter ℂ p, ψ⁻¹ a * ψ l * ψ⁻¹ k := by
      simp only [gaussSum,sum_mul,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro ψ hψ
      ring
    _ = _ := by simp_rw [horth]; simp [mul_comm]

/-- The principal prime-modulus Gauss sum is exactly -1. -/
theorem proposition71_principal_gauss {p : ℕ} [NeZero p] (hp : p.Prime) :
    gaussSum (1 : DirichletCharacter ℂ p) ZMod.stdAddChar = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have he : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
    have h := ZMod.isPrimitive_stdAddChar p (one_ne_zero : (1 : ZMod p) ≠ 0)
    simpa using h
  have ht (a : ZMod p) :
      (1 : DirichletCharacter ℂ p) a * ZMod.stdAddChar a =
        ZMod.stdAddChar a - if a = 0 then 1 else 0 := by
    by_cases ha : a = 0
    · subst a
      simp [DirichletCharacter.map_zero' _ hp.ne_one]
    · simp [MulChar.one_apply,isUnit_iff_ne_zero,ha]
  simp only [gaussSum,ht,sum_sub_distrib]
  rw [AddChar.sum_eq_zero_of_ne_one he]
  simp

/-- The exact primitive-character identity underlying (7.7), including the
principal-character correction that is hidden in the paper's O(1). -/
theorem proposition71_primitive_gauss_average {p : ℕ} [NeZero p] (hp : p.Prime)
    (l k : ZMod p) (hl : IsUnit l) (hk : IsUnit k) :
    (∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter
      (fun ψ => ψ.IsPrimitive), gaussSum ψ⁻¹ ZMod.stdAddChar * ψ l * ψ⁻¹ k) =
      (p.totient : ℂ) * ZMod.stdAddChar (l * k⁻¹) + 1 := by
  have hf : (univ : Finset (DirichletCharacter ℂ p)).filter
      (fun ψ => ψ.IsPrimitive) = univ.erase 1 := by
    ext ψ
    simp [proposition71_prime_primitive_iff hp]
  rw [hf,sum_erase_eq_sub (mem_univ _),proposition71_full_gauss_average hp l k hl hk]
  simp [proposition71_principal_gauss hp,MulChar.one_apply,hl,hk]

/-- Uniform O(1) in the paper's displayed Gauss average, with explicit constant 2. -/
theorem proposition71_primitive_gauss_error {p : ℕ} [NeZero p] (hp : p.Prime)
    (l k : ZMod p) (hl : IsUnit l) (hk : IsUnit k) :
    ‖(∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter
      (fun ψ => ψ.IsPrimitive), gaussSum ψ⁻¹ ZMod.stdAddChar * ψ l * ψ⁻¹ k) -
      (p : ℂ) * ZMod.stdAddChar (l * k⁻¹)‖ ≤ 2 := by
  rw [proposition71_primitive_gauss_average hp l k hl hk]
  have ht : (p.totient : ℂ) = (p : ℂ) - 1 := by
    rw [Nat.totient_prime hp,Nat.cast_sub hp.one_le]
    simp
  rw [ht]
  have he : ((p : ℂ)-1)*ZMod.stdAddChar (l*k⁻¹)+1-
      (p : ℂ)*ZMod.stdAddChar (l*k⁻¹) = 1-ZMod.stdAddChar (l*k⁻¹) := by ring
  rw [he]
  have hn : ‖ZMod.stdAddChar (l*k⁻¹)‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hh := norm_sub_le (1 : ℂ) (ZMod.stdAddChar (l*k⁻¹))
  rw [hn,norm_one] at hh
  norm_num at hh ⊢
  exact hh

/-- The nonunit branch is zero, not the unit-formula with totalized division. -/
theorem proposition71_gauss_average_nonunit {p : ℕ} [NeZero p]
    (l k : ZMod p) (h : ¬IsUnit l ∨ ¬IsUnit k) :
    (∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter
      (fun ψ => ψ.IsPrimitive), gaussSum ψ⁻¹ ZMod.stdAddChar * ψ l * ψ⁻¹ k) = 0 := by
  apply sum_eq_zero
  intro ψ hψ
  rcases h with hl | hk
  · rw [MulChar.map_nonunit ψ hl,mul_zero,zero_mul]
  · rw [MulChar.map_nonunit ψ⁻¹ hk,mul_zero]

/-- Both branches of the genuine primitive-prime average are retained. -/
theorem proposition71_primitive_gauss_average_all {p : ℕ} [NeZero p] (hp : p.Prime)
    (l k : ZMod p) :
    (∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter
      (fun ψ => ψ.IsPrimitive), gaussSum ψ⁻¹ ZMod.stdAddChar * ψ l * ψ⁻¹ k) =
      if IsUnit l ∧ IsUnit k then
        (p.totient : ℂ)*ZMod.stdAddChar (l*k⁻¹)+1 else 0 := by
  split_ifs with h
  · exact proposition71_primitive_gauss_average hp l k h.1 h.2
  · exact proposition71_gauss_average_nonunit l k (not_and_or.mp h)

end ZhangLS.Spec
