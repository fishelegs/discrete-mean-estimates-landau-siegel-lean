import ZhangLS.Spec.Lemma31
import ZhangLS.Spec.Lemma34DivisorFunction
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32ActualCoefficient {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) : ℝ :=
  ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2

lemma lemma32_actual_coefficient_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    0 ≤ lemma32ActualCoefficient χ n := mul_nonneg (sq_nonneg _) (sq_nonneg _)

lemma lemma32_tau_two_prime_power {p : ℕ} (hp : p.Prime) (e : ℕ) :
    lemma34Tau 2 (p^e) = e+1 := by
  have h := lemma34_tau_prime_power hp 1 e
  simpa [Nat.multichoose_eq,Nat.add_comm] using h

lemma lemma32_actual_coefficient_prime_power_of_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 1) (e : ℕ) :
    lemma32ActualCoefficient χ (p^e) = (e+1 : ℝ)^4 := by
  unfold lemma32ActualCoefficient
  rw [← lemma31_nu_real_eq_norm χ (p^e)]
  unfold lemma31NuReal
  rw [lemma31_actual_nu_prime_power_of_one χ hp h e,lemma32_tau_two_prime_power hp e]
  simp only [Complex.add_re,Complex.natCast_re,Complex.one_re,Nat.cast_add,Nat.cast_one]
  ring

lemma lemma32_actual_coefficient_prime_power_of_zero {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 0) (e : ℕ) :
    lemma32ActualCoefficient χ (p^e) = (e+1 : ℝ)^2 := by
  unfold lemma32ActualCoefficient
  rw [lemma31_actual_nu_prime_power χ hp e,h,lemma32_tau_two_prime_power hp e]
  simp [zero_pow_eq]

lemma lemma32_actual_coefficient_prime_power_of_neg_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = -1) (e : ℕ) :
    lemma32ActualCoefficient χ (p^e) = if Even (e+1) then 0 else (e+1 : ℝ)^2 := by
  unfold lemma32ActualCoefficient
  rw [lemma31_actual_nu_prime_power χ hp e,h,neg_one_geom_sum,lemma32_tau_two_prime_power hp e]
  split_ifs <;> simp

lemma lemma32_actual_coefficient_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma32ActualCoefficient χ 1 = 1 := by
  unfold lemma32ActualCoefficient lemma34Tau
  simp [lemma31_actual_nu_one,ArithmeticFunction.IsMultiplicative.map_one
    (lemma34_tau_multiplicative 2)]

end ZhangLS.Spec
