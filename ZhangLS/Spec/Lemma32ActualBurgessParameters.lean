import ZhangLS.Spec.Lemma32BurgessCollisionParameters
import ZhangLS.Spec.Lemma32BurgessShiftAmplification
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_burgess_unit_power_exp (D : ℕ) :
    lemma32BurgessPower D (1/2048)=Real.exp (Real.log (D : ℝ)/2048) := by
  unfold lemma32BurgessPower
  congr 1
  ring

lemma lemma32_actual_burgess_chosen_unit_lower {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1≤D)
    (hN : lemma32BurgessSmallRangeConstant*lemma32BurgessPower D (25/64)<(N : ℝ)) :
    (lemma32BurgessMultiplierLength D N : ℝ)/(2*lemma32UnitPrimeSavingConstant*lemma32BurgessPower D (1/2048)) ≤
      ((lemma32BurgessUnitMultipliers D (lemma32BurgessMultiplierLength D N)).card : ℝ) := by
  have hA := (lemma32_burgess_multiplier_length_bounds hD hN).2.2.2
  rw [lemma32_burgess_unit_power_exp] at hA ⊢
  exact lemma32_actual_primitive_unit_multiplier_power_lower χ _ hA

lemma lemma32_actual_burgess_chosen_unit_count_pos {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1≤D)
    (hN : lemma32BurgessSmallRangeConstant*lemma32BurgessPower D (25/64)<(N : ℝ)) :
    0<(lemma32BurgessUnitMultipliers D (lemma32BurgessMultiplierLength D N)).card := by
  have hA := (lemma32_burgess_multiplier_length_bounds hD hN).1
  have hAR : (0 : ℝ)<(lemma32BurgessMultiplierLength D N : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hd : (0 : ℝ)<2*lemma32UnitPrimeSavingConstant*lemma32BurgessPower D (1/2048) :=
    mul_pos (mul_pos (by norm_num) lemma32_unit_prime_saving_constant_pos)
      (lemma32_burgess_power_pos D (1/2048))
  have hu := (div_pos hAR hd).trans_le (lemma32_actual_burgess_chosen_unit_lower χ hD hN)
  exact Nat.cast_pos.mp hu

lemma lemma32_actual_burgess_chosen_amplification {D N : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (hD : 1≤D)
    (hN : lemma32BurgessSmallRangeConstant*lemma32BurgessPower D (25/64)<(N : ℝ))
    (hupper : (N : ℝ)≤lemma32BurgessPower D (79/128)) (M : ℤ) :
    (lemma32BurgessShiftAbsoluteSum χ M (lemma32BurgessMultiplierLength D N) N (lemma32BurgessBlockLength D))^4 ≤
      ((lemma32BurgessMultiplierLength D N : ℝ)*(N : ℝ))^2 *
      (3*(lemma32BurgessMultiplierLength D N : ℝ)*(N : ℝ)*
        (1+Real.log (lemma32BurgessMultiplierLength D N : ℝ))) *
      (3*(D : ℝ)*(lemma32BurgessBlockLength D : ℝ)^2 + lemma32UniformMomentConstant*
        lemma32BurgessPower D (17/32)*(lemma32BurgessBlockLength D : ℝ)^4) :=
  lemma32_actual_burgess_amplification_fourth_bound χ
    (lemma32_burgess_collision_parameter_bound hD hupper)
    (lemma32_burgess_multiplier_length_le_interval hD)
    (lemma32_burgess_multiplier_length_bounds hD hN).1 M

end ZhangLS.Spec
