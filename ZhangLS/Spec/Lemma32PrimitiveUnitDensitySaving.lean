import ZhangLS.Spec.Lemma32UnitMultiplierLower
import ZhangLS.Spec.Lemma32UnitPrimePowerSaving
import ZhangLS.Spec.Lemma32PrimitiveDivisorCount
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical

lemma lemma32_actual_primitive_unit_error_power_saving {D : ℕ}
    (χ : RealPrimitiveCharacter D) :
    (2 : ℝ)^D.primeFactors.card*(D.divisors.card : ℝ) ≤
      lemma32UnitPrimeSavingConstant*Real.exp (Real.log (D : ℝ)/2048) := by
  have ht : (D.divisors.card : ℝ) ≤ (4 : ℝ)^D.primeFactors.card := by
    exact_mod_cast lemma32_actual_primitive_divisor_count χ
  calc
    _ ≤ (2 : ℝ)^D.primeFactors.card*(4 : ℝ)^D.primeFactors.card :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (8 : ℝ)^D.primeFactors.card := by rw [← mul_pow];norm_num
    _ ≤ _ := lemma32_unit_prime_factor_power_bound D χ.modulus_pos

lemma lemma32_actual_primitive_unit_multiplier_power_lower {D : ℕ}
    (χ : RealPrimitiveCharacter D) (A : ℕ)
    (hlarge : 2*lemma32UnitPrimeSavingConstant*Real.exp (Real.log (D : ℝ)/2048) ≤
      (A : ℝ)) :
    (A : ℝ)/(2*lemma32UnitPrimeSavingConstant*Real.exp (Real.log (D : ℝ)/2048)) ≤
      ((lemma32BurgessUnitMultipliers D A).card : ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (lemma32_actual_primitive_unit_error_power_saving χ)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hh' : 2*(2 : ℝ)^D.primeFactors.card*(D.divisors.card : ℝ) ≤
      2*lemma32UnitPrimeSavingConstant*Real.exp (Real.log (D : ℝ)/2048) := by
    simpa only [mul_assoc] using hh
  have hl : 2*(2 : ℝ)^D.primeFactors.card*(D.divisors.card : ℝ) ≤ (A : ℝ) :=
    hh'.trans hlarge
  have hp : (2 : ℝ)^D.primeFactors.card ≤
      lemma32UnitPrimeSavingConstant*Real.exp (Real.log (D : ℝ)/2048) :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 8) _).trans
      (lemma32_unit_prime_factor_power_bound D χ.modulus_pos)
  calc
    _ ≤ (A : ℝ)/(2*(2 : ℝ)^D.primeFactors.card) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (by nlinarith)
    _ ≤ _ := lemma32_actual_burgess_unit_multiplier_lower χ.modulus_pos A hl

end ZhangLS.Spec
