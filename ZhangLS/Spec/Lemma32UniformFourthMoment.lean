import ZhangLS.Spec.Lemma32CompositeFourthMoment
import ZhangLS.Spec.Lemma32PrimitiveDivisorCount
import ZhangLS.Spec.Lemma32PrimeFactorPower
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical

noncomputable def lemma32UniformMomentConstant : ℝ := 256 * lemma32MomentPrimeSavingConstant

lemma lemma32_uniform_moment_constant_pos : 0 < lemma32UniformMomentConstant := by
  unfold lemma32UniformMomentConstant
  exact mul_pos (by norm_num) lemma32_moment_prime_saving_constant_pos

lemma lemma32_actual_uniform_burgess_fourth_moment {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) :
    lemma32BurgessFourthMoment χ H ≤
      3*(D : ℝ)*(H : ℝ)^2 +
      lemma32UniformMomentConstant * Real.exp ((17/32)*Real.log (D : ℝ))*(H : ℝ)^4 := by
  have hf := (lemma32_actual_primitive_moment_divisor_factor χ).trans
    (lemma32_moment_prime_factor_power_bound D χ.modulus_pos)
  have hs : Real.sqrt (D : ℝ) = Real.exp (Real.log (D : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Nat.cast_pos.mpr χ.modulus_pos)]
    congr 1
    ring
  have he := mul_le_mul_of_nonneg_left hf
    (by positivity : (0 : ℝ) ≤ 256*Real.sqrt (D : ℝ)*(H : ℝ)^4)
  have hb : 256*(3 : ℝ)^D.primeFactors.card*Real.sqrt (D : ℝ)*(H : ℝ)^4*
      (D.divisors.card : ℝ)^3 ≤
      lemma32UniformMomentConstant*Real.exp ((17/32)*Real.log (D : ℝ))*(H : ℝ)^4 := by
    calc
      _ = (256*Real.sqrt (D : ℝ)*(H : ℝ)^4)*
          ((3 : ℝ)^D.primeFactors.card*(D.divisors.card : ℝ)^3) := by ring
      _ ≤ (256*Real.sqrt (D : ℝ)*(H : ℝ)^4)*
          (lemma32MomentPrimeSavingConstant*Real.exp (Real.log (D : ℝ)/32)) := he
      _ = _ := by
        rw [hs]
        unfold lemma32UniformMomentConstant
        have hex : Real.exp (Real.log (D : ℝ)/2)*Real.exp (Real.log (D : ℝ)/32) =
            Real.exp ((17/32)*Real.log (D : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = (256*lemma32MomentPrimeSavingConstant)*
              (Real.exp (Real.log (D : ℝ)/2)*Real.exp (Real.log (D : ℝ)/32))*(H : ℝ)^4 := by ring
          _ = _ := by rw [hex]
  exact (lemma32_actual_composite_burgess_fourth_moment χ H).trans (add_le_add le_rfl hb)

end ZhangLS.Spec
