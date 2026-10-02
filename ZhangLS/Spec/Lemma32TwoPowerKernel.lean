import ZhangLS.Spec.Lemma32OddPrimePowerConductor
import Mathlib.RingTheory.ZMod.UnitsCyclic
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000

def lemma32TwoPowerReductionDvd (k : ℕ) : 8 ∣ 2^(k+3) := by
  change 2^3 ∣ 2^(k+3)
  exact pow_dvd_pow 2 (by omega)

noncomputable def lemma32TwoPowerFiveUnit (k : ℕ) : (ZMod (2^(k+3)))ˣ :=
  ZMod.unitOfCoprime 5 ((by decide : Nat.Coprime 5 2).pow_right (k+3))

lemma lemma32_two_power_reduction_kernel_card (k : ℕ) :
    Nat.card (ZMod.unitsMap (lemma32TwoPowerReductionDvd k)).ker = 2^k := by
  letI : NeZero (2^(k+3)) := ⟨pow_ne_zero _ (by decide)⟩
  have he := lemma32_units_reduction_kernel_card (lemma32TwoPowerReductionDvd k)
  rw [Nat.totient_prime_pow_succ Nat.prime_two (k+2)] at he
  have he' : Nat.card (ZMod.unitsMap (lemma32TwoPowerReductionDvd k)).ker * 4 = 2^k*4 := by
    simpa only [show Nat.totient 8=4 from by decide, pow_add, Nat.reducePow,
      Nat.reduceSub, mul_one] using he
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 4) he'

lemma lemma32_two_power_five_unit_order (k : ℕ) :
    orderOf (lemma32TwoPowerFiveUnit k) = 2^(k+1) := by
  rw [← orderOf_units]
  simpa only [lemma32TwoPowerFiveUnit, ZMod.coe_unitOfCoprime,
    Nat.cast_ofNat] using ZMod.orderOf_five (k+1)

lemma lemma32_two_power_five_square_order (k : ℕ) :
    orderOf (lemma32TwoPowerFiveUnit k ^ 2) = 2^k := by
  have hd : 2 ∣ orderOf (lemma32TwoPowerFiveUnit k) := by
    rw [lemma32_two_power_five_unit_order]
    exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  rw [orderOf_pow_of_dvd (by decide) hd, lemma32_two_power_five_unit_order, pow_succ]
  exact Nat.mul_div_cancel _ (by decide)

end ZhangLS.Spec
