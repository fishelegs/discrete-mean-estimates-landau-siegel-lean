import ZhangLS.Spec.Lemma32BurgessReduction
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32ResidueShortSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (H : ℕ) (x : ZMod D) : ℂ := ∑ h : Fin H, χ.chi (x+(h.val : ZMod D))

noncomputable def lemma32BurgessFourthMoment {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) : ℝ := ∑ x : ZMod D, ‖lemma32ResidueShortSum χ H x‖^4

noncomputable def lemma32QuarticCorrelation {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) {H : ℕ} (v : Fin 4 → Fin H) : ℝ :=
  ∑ x : ZMod D, (χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod D)))).re

lemma lemma32_real_complex_norm_fourth (z : ℂ) (hz : z.im = 0) : ‖z‖^4 = z.re^4 := by
  calc
    _ = (‖z‖^2)^2 := by ring
    _ = (z.re^2)^2 := by rw [Complex.sq_norm,Complex.normSq_apply,hz];ring
    _ = _ := by ring

lemma lemma32_actual_quartic_character_product {D : ℕ} (χ : RealPrimitiveCharacter D)
    {H : ℕ} (v : Fin 4 → Fin H) (x : ZMod D) :
    (χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod D)))).re =
      ∏ i : Fin 4, (χ.chi (x+((v i).val : ZMod D))).re := by
  have he (i : Fin 4) : χ.chi (x+((v i).val : ZMod D)) =
      ((χ.chi (x+((v i).val : ZMod D))).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [χ.real_valued]
  rw [map_prod]
  have hp : (∏ i : Fin 4, χ.chi (x+((v i).val : ZMod D))) =
      ∏ i : Fin 4, ((χ.chi (x+((v i).val : ZMod D))).re : ℂ) :=
    Finset.prod_congr rfl (fun i hi => he i)
  rw [hp]
  rw [← Complex.ofReal_prod]
  rfl

lemma lemma32_actual_burgess_fourth_moment_expansion {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) :
    lemma32BurgessFourthMoment χ H = ∑ v : Fin 4 → Fin H, lemma32QuarticCorrelation χ v := by
  have hx (x : ZMod D) : ‖lemma32ResidueShortSum χ H x‖^4 =
      ∑ v : Fin 4 → Fin H, ∏ i : Fin 4, (χ.chi (x+((v i).val : ZMod D))).re := by
    rw [lemma32_real_complex_norm_fourth _ (by
      simp only [lemma32ResidueShortSum,Complex.im_sum,χ.real_valued,Finset.sum_const_zero])]
    simp only [lemma32ResidueShortSum,Complex.re_sum]
    exact Fintype.sum_pow _ 4
  unfold lemma32BurgessFourthMoment lemma32QuarticCorrelation
  simp_rw [hx]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro x hx
  exact (lemma32_actual_quartic_character_product χ v x).symm

end ZhangLS.Spec
