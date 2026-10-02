import ZhangLS.Spec.Lemma152WeightedSupported
import ZhangLS.Spec.Lemma161XiPrimePower
import ZhangLS.Spec.Lemma83LocalAgreement

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

lemma lemma161_character_arithmetic_eq {D n : ℕ} (χ : RealPrimitiveCharacter D)
    (hn : n ≠ 0) : lemma23CharacterArithmeticFunction χ n = χ.evalNat n := by
  simp [lemma23CharacterArithmeticFunction,toArithmeticFunction,hn,RealPrimitiveCharacter.evalNat]

lemma lemma161_weighted_local_excluded_hasSum (f w : ArithmeticFunction ℂ)
    (hw : w 1 = 1) (d m : ℕ) (s : ℂ) (p : ℕ) (hpm : p ∣ m) :
    HasSum (lemma152WeightedModifiedLocal f w d m s p) (f (p^(d.factorization p))) := by
  convert hasSum_ite_eq 0 (f (p^(d.factorization p))) using 1
  funext e
  by_cases he : e = 0 <;> simp [lemma152WeightedModifiedLocal,hpm,he,hw]

lemma lemma161_weighted_local_kappa_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d m : ℕ) (s : ℂ)
    (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    Summable (fun e => ‖lemma152WeightedModifiedLocal (lemma161Kappa β)
      (lemma23CharacterArithmeticFunction χ) d m s p e‖) := by
  by_cases hpm : p ∣ m
  · exact summable_norm_iff.mpr (lemma161_weighted_local_excluded_hasSum
      (lemma161Kappa β) (lemma23CharacterArithmeticFunction χ)
      (χ.chi.isMultiplicative_toArithmeticFunction.map_one) d m s p hpm).summable
  · have ht : ‖χ.evalNat p*(p:ℂ)^(-s)‖ < 1 := by
      rw [norm_mul]
      apply lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p))
      rw [← lemma32_prime_monomial_eq_cpow hp.pos]
      exact lemma32_prime_monomial_norm_lt_one hp.one_lt s hs
    have hq : ‖(p:ℂ)^(-β)*(χ.evalNat p*(p:ℂ)^(-s))‖ < 1 := by
      simpa [norm_mul,lemma83_cpow_shift_norm hp.pos β hβ] using ht
    have hh := lemma83_power_series_shifted_summable
      (lemma152LocalKappa ((p:ℂ)^(-β)) 0)
      (χ.evalNat p*(p:ℂ)^(-s)) (d.factorization p)
      (lemma152_local_kappa_hasSum _ _ _ hq (by simp)).summable
    apply summable_norm_iff.mpr
    convert hh using 1
    funext e
    simp only [lemma152WeightedModifiedLocal,hpm,false_and,if_false,
      lemma161_kappa_prime_power β hp,
      lemma161_character_arithmetic_eq χ (pow_ne_zero e hp.ne_zero),mul_pow]
    simp [RealPrimitiveCharacter.evalNat,Nat.cast_pow,map_pow,mul_assoc]

/-- Absolute convergence of the actual weighted supported series. -/
lemma lemma161_modified_kappa_hasSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d m : ℕ) (hd : d ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun h : Lemma83SupportedIndex d m =>
      lemma161Kappa β (d*h.val)*χ.evalNat h.val/(h.val:ℂ)^s)
      (∏ p ∈ d.primeFactors, ∑' e : ℕ, lemma152WeightedModifiedLocal (lemma161Kappa β)
        (lemma23CharacterArithmeticFunction χ) d m s p e) := by
  have hh := lemma152_weighted_modified_supported_hasSum (lemma161Kappa β)
    (lemma23CharacterArithmeticFunction χ) (lemma161_kappa_multiplicative β)
    χ.chi.isMultiplicative_toArithmeticFunction d m hd s
    (fun p hp => lemma161_weighted_local_kappa_summable χ β hβ d m s hs
      (Nat.prime_of_mem_primeFactors hp))
  convert hh using 1
  funext h
  rw [lemma161_character_arithmetic_eq χ h.property.1]

/-- Exact finite Euler product of the Section16 supported sum. No division by κ₂(d) or χ(d). -/
lemma lemma161_modified_kappa_product {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d m : ℕ) (hd : d ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    lemma161ModifiedKappa χ β d m s = ∏ p ∈ d.primeFactors,
      if p ∣ m then lemma161Kappa β (p^(d.factorization p)) else
        ∑' e : ℕ, lemma161Kappa β (p^(d.factorization p+e))*
          (χ.evalNat p*(p:ℂ)^(-s))^e := by
  rw [lemma161ModifiedKappa,(lemma161_modified_kappa_hasSum χ β hβ d m hd s hs).tsum_eq]
  apply prod_congr rfl
  intro p hp
  have hp0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
  by_cases hpm : p ∣ m
  · rw [if_pos hpm,(lemma161_weighted_local_excluded_hasSum (lemma161Kappa β)
      (lemma23CharacterArithmeticFunction χ) χ.chi.isMultiplicative_toArithmeticFunction.map_one
      d m s p hpm).tsum_eq]
  · simp only [if_neg hpm,lemma152WeightedModifiedLocal,hpm,false_and,if_false,
      lemma161_character_arithmetic_eq χ (pow_ne_zero _ hp0)]
    apply tsum_congr
    intro e
    simp [RealPrimitiveCharacter.evalNat,Nat.cast_pow,map_pow,mul_pow,mul_assoc]

end ZhangLS.Spec
