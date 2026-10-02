import ZhangLS.Spec.Lemma32BurgessMultiplierParameters
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical

lemma lemma32_burgess_collision_parameter_bound {D N : ℕ} (hD : 1≤D)
    (hN : (N : ℝ)≤lemma32BurgessPower D (79/128)) :
    2*lemma32BurgessMultiplierLength D N*N<D := by
  have hDpos : 0<D := Nat.lt_of_lt_of_le Nat.zero_lt_one hD
  have hb := lemma32_burgess_block_bounds hD
  have hab := lemma32_burgess_shift_product_bound (N := N) hD
  have hab' : (lemma32BurgessMultiplierLength D N : ℝ)*
      (lemma32BurgessBlockLength D : ℝ)*1024≤(N : ℝ) :=
    (le_div_iff₀ (by norm_num : (0 : ℝ)<1024)).mp hab
  have haux := mul_le_mul_of_nonneg_right hab'
    (by positivity : (0 : ℝ)≤2*(N : ℝ))
  have he : (lemma32BurgessPower D (79/128))^2 =
      (D : ℝ)*lemma32BurgessPower D (15/64) := by
    rw [lemma32_burgess_power_nat_pow, ← lemma32_burgess_power_one hDpos,
      ← lemma32_burgess_power_add]
    norm_num
  have hn : (N : ℝ)^2≤(D : ℝ)*lemma32BurgessPower D (15/64) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2).trans_eq he
  have hcoef0 : (0 : ℝ)≤1024*(lemma32BurgessMultiplierLength D N : ℝ)*(N : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hB : lemma32BurgessPower D (15/64)≤2*(lemma32BurgessBlockLength D : ℝ) := by
    linarith [hb.2.1]
  have hc : (1024*(lemma32BurgessMultiplierLength D N : ℝ)*(N : ℝ))*lemma32BurgessPower D (15/64) ≤
      (2*(D : ℝ))*lemma32BurgessPower D (15/64) := by
    calc
      _ ≤ (1024*(lemma32BurgessMultiplierLength D N : ℝ)*(N : ℝ))*
          (2*(lemma32BurgessBlockLength D : ℝ)) := mul_le_mul_of_nonneg_left hB hcoef0
      _ ≤ 2*(N : ℝ)^2 := by nlinarith [haux]
      _ ≤ 2*((D : ℝ)*lemma32BurgessPower D (15/64)) :=
        mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = _ := by ring
  have hg := (mul_le_mul_iff_left₀ (lemma32_burgess_power_pos D (15/64))).mp hc
  have hDR : (0 : ℝ)<(D : ℝ) := Nat.cast_pos.mpr hDpos
  have hR : 2*(lemma32BurgessMultiplierLength D N : ℝ)*(N : ℝ)<(D : ℝ) := by nlinarith
  exact_mod_cast hR

end ZhangLS.Spec
