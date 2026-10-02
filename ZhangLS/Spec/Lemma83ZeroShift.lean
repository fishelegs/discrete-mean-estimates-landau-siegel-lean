import ZhangLS.Spec.Lemma83ExceptionalProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma83_prime_monomial_one {p : ℕ} (hp : 0 < p) :
    lemma32PrimeMonomial p 1 = (p:ℂ)⁻¹ := by
  rw [lemma32_prime_monomial_eq_cpow hp,Complex.cpow_neg_one]

lemma lemma83_exceptional_prime_zero_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (r : ℕ) {p : ℕ} (hp : p.Prime) :
    lemma83ExceptionalPrimeFactor χ 0 r p 1 =
      (1-χ.evalNat p/(p:ℂ))⁻¹ *
        if p ∣ r then 1 else (1-(p:ℂ)⁻¹-χ.evalNat p/(p:ℂ))/(1-(p:ℂ)⁻¹) := by
  have hn : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpn : (p:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  have hu : 1-(p:ℂ)⁻¹ ≠ 0 := by
    have he : 1-(p:ℂ)⁻¹ = ((p:ℂ)-1)/(p:ℂ) := by field_simp <;> ring
    rw [he]
    exact div_ne_zero hpn hn
  unfold lemma83ExceptionalPrimeFactor
  rw [lemma83_prime_monomial_one hp.pos]
  simp only [lemma32PrimeMonomial,mul_zero,zero_mul,neg_zero,Complex.exp_zero]
  split_ifs
  · simp [lemma83RCorrection,div_eq_mul_inv]
  · unfold lemma83DCorrection
    simp only [one_mul]
    have ht : 1-χ.evalNat p*(p:ℂ)⁻¹/(1-(p:ℂ)⁻¹) =
        (1-(p:ℂ)⁻¹-χ.evalNat p/(p:ℂ))/(1-(p:ℂ)⁻¹) := by
      field_simp [hu,hn]
      all_goals ring
    rw [ht]
    simp [div_eq_mul_inv,mul_comm]

lemma lemma83_exceptional_prime_set (d r : ℕ) (hd : d ≠ 0) (hr : r ≠ 0) :
    (d*r).primeFactors.filter (fun p => ¬p ∣ r) =
      d.primeFactors.filter (fun p => ¬p ∣ r) := by
  ext p
  simp only [mem_filter,Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp,hpd,_⟩,hpr⟩
    exact ⟨⟨hp,(hp.dvd_mul.mp hpd).resolve_right hpr,hd⟩,hpr⟩
  · rintro ⟨⟨hp,hpd,_⟩,hpr⟩
    exact ⟨⟨hp,hpd.trans (dvd_mul_right d r),mul_ne_zero hd hr⟩,hpr⟩

/-- Exact Π, including its possibly vanishing q=2 factor. -/
lemma lemma83_exceptional_product_zero_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (d r : ℕ) (hd : d ≠ 0) (hr : r ≠ 0) :
    lemma83ExceptionalEulerProduct χ 0 d r 1 = lemma83Pi χ d r := by
  unfold lemma83ExceptionalEulerProduct lemma83Pi
  rw [show (∏ p ∈ (d*r).primeFactors, lemma83ExceptionalPrimeFactor χ 0 r p 1) =
      ∏ p ∈ (d*r).primeFactors, (1-χ.evalNat p/(p:ℂ))⁻¹ *
        if p ∣ r then 1 else (1-(p:ℂ)⁻¹-χ.evalNat p/(p:ℂ))/(1-(p:ℂ)⁻¹) from
    prod_congr rfl (fun p hp => lemma83_exceptional_prime_zero_shift χ r
      (Nat.prime_of_mem_primeFactors hp))]
  rw [prod_mul_distrib]
  congr 1
  simp_rw [← ite_not (p := _ ∣ r)]
  rw [← Finset.prod_filter,lemma83_exceptional_prime_set d r hd hr]

lemma lemma83_euler_correction_zero_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (j : Fin 3) (d r : ℕ) (hd : d ≠ 0) (hr : r ≠ 0) :
    lemma83EulerCorrection χ (fun _ => 0) j d r 1 = lemma83Pi χ d r := by
  simp [lemma83EulerCorrection,lemma83_exceptional_product_zero_shift χ d r hd hr]

end ZhangLS.Spec
