import ZhangLS.Spec.Lemma32PrimitivePolyaVinogradov
import ZhangLS.Spec.Lemma32BurgessPowerAlgebra
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical

lemma lemma32_actual_burgess_short_interval_bound {D : ℕ}
    (χ : RealPrimitiveCharacter D) (M : ℤ) (N : ℕ) {C : ℝ} (hC : 0≤C)
    (hN : (N : ℝ)≤C^2*lemma32BurgessPower D (25/64)) :
    ‖lemma32BurgessIntervalSum χ M N‖ ≤
      C*lemma32BurgessPower D (25/128)*Real.sqrt (N : ℝ) := by
  have hp := lemma32_burgess_power_pos D (25/128)
  have he : (lemma32BurgessPower D (25/128))^2=lemma32BurgessPower D (25/64) := by
    rw [lemma32_burgess_power_nat_pow]
    norm_num
  rw [← he] at hN
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ)≤(N : ℝ))
  have hn := Real.sqrt_nonneg (N : ℝ)
  have hc : 0≤C*lemma32BurgessPower D (25/128) := mul_nonneg hC hp.le
  have hroot : Real.sqrt (N : ℝ)≤C*lemma32BurgessPower D (25/128) := by nlinarith
  exact (lemma32_actual_character_interval_trivial χ M N).trans (by nlinarith)

lemma lemma32_actual_burgess_long_interval_bound {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (M : ℤ) (N : ℕ)
    (hN : lemma32BurgessPower D (79/128)≤(N : ℝ)) :
    ‖lemma32BurgessIntervalSum χ M N‖ ≤
      1024*lemma32BurgessPower D (25/128)*Real.sqrt (N : ℝ) := by
  have hp : (lemma32BurgessPower D (79/256))^2=lemma32BurgessPower D (79/128) := by
    rw [lemma32_burgess_power_nat_pow]
    norm_num
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ)≤(N : ℝ))
  have hroot : lemma32BurgessPower D (79/256)≤Real.sqrt (N : ℝ) := by
    have hpos := lemma32_burgess_power_pos D (79/256)
    have hn := Real.sqrt_nonneg (N : ℝ)
    rw [← hp] at hN
    nlinarith
  have hlog := mul_le_mul_of_nonneg_left (lemma32_burgess_log_power_bound D)
    (by positivity : (0 : ℝ)≤2*Real.sqrt (D : ℝ))
  have he : 2*Real.sqrt (D : ℝ)*(512*lemma32BurgessPower D (1/512)) =
      1024*lemma32BurgessPower D (257/512) := by
    rw [lemma32_burgess_power_sqrt χ.modulus_pos]
    have ht : lemma32BurgessPower D (1/2)*lemma32BurgessPower D (1/512)=
        lemma32BurgessPower D (257/512) := by
      rw [← lemma32_burgess_power_add]
      norm_num
    calc
      _ = 1024*(lemma32BurgessPower D (1/2)*lemma32BurgessPower D (1/512)) := by ring
      _ = _ := by rw [ht]
  rw [he] at hlog
  have hm := mul_le_mul_of_nonneg_left
    (lemma32_burgess_power_mono hD.le (by norm_num : (257/512 : ℝ)≤129/256))
    (by norm_num : (0 : ℝ)≤1024)
  have ha : lemma32BurgessPower D (129/256)=
      lemma32BurgessPower D (25/128)*lemma32BurgessPower D (79/256) := by
    rw [← lemma32_burgess_power_add]
    norm_num
  rw [ha] at hm
  have hlast : 1024*(lemma32BurgessPower D (25/128)*lemma32BurgessPower D (79/256)) ≤
      1024*lemma32BurgessPower D (25/128)*Real.sqrt (N : ℝ) := by
    calc
      _ = (1024*lemma32BurgessPower D (25/128))*lemma32BurgessPower D (79/256) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot
        (mul_nonneg (by norm_num) (lemma32_burgess_power_pos D (25/128)).le)
  exact ((lemma32_actual_primitive_polya_vinogradov χ hD M N).trans hlog).trans
    (hm.trans hlast)

end ZhangLS.Spec
