import ZhangLS.Spec.Lemma32UniformFourthMoment
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def lemma32BurgessIntervalSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (M : ℤ) (N : ℕ) : ℂ :=
  ∑ i : Fin N, χ.chi (((M+(i.val : ℤ)) : ℤ) : ZMod D)

lemma lemma32_actual_coprime_character_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (a : ℕ) (ha : a.Coprime D) : ‖χ.chi (a : ZMod D)‖ = 1 := by
  rw [← ZMod.coe_unitOfCoprime a ha]
  exact χ.chi.unit_norm_eq_one _

lemma lemma32_actual_burgess_shift_character {D : ℕ} (χ : RealPrimitiveCharacter D)
    (a : ℕ) (ha : a.Coprime D) (x b : ZMod D) :
    χ.chi (x+(a : ZMod D)*b) =
      χ.chi (a : ZMod D) * χ.chi ((a : ZMod D)⁻¹*x+b) := by
  have hu : IsUnit (a : ZMod D) := (ZMod.isUnit_iff_coprime a D).mpr ha
  have he : x+(a : ZMod D)*b = (a : ZMod D)*((a : ZMod D)⁻¹*x+b) := by
    rw [mul_add, ← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]
  rw [he, map_mul]

lemma lemma32_actual_burgess_shift_short_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (a : ℕ) (ha : a.Coprime D) (B : ℕ) (x : ZMod D) :
    (∑ b : Fin B, χ.chi (x+(a : ZMod D)*(b.val : ZMod D))) =
      χ.chi (a : ZMod D) * lemma32ResidueShortSum χ B ((a : ZMod D)⁻¹*x) := by
  simp_rw [lemma32_actual_burgess_shift_character χ a ha]
  exact (Finset.mul_sum _ _ _).symm

lemma lemma32_actual_burgess_shift_short_sum_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (a : ℕ) (ha : a.Coprime D) (B : ℕ) (x : ZMod D) :
    ‖∑ b : Fin B, χ.chi (x+(a : ZMod D)*(b.val : ZMod D))‖ =
      ‖lemma32ResidueShortSum χ B ((a : ZMod D)⁻¹*x)‖ := by
  rw [lemma32_actual_burgess_shift_short_sum χ a ha, norm_mul,
    lemma32_actual_coprime_character_norm χ a ha, one_mul]

end ZhangLS.Spec
