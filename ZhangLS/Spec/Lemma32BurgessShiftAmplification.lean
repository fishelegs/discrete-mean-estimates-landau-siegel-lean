import ZhangLS.Spec.Lemma32BurgessWeightedMoment
import ZhangLS.Spec.Lemma32BurgessMultiplicityEnergy
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def lemma32BurgessShiftAbsoluteSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (M : ℤ) (A N B : ℕ) : ℝ :=
  ∑ p ∈ lemma32BurgessMultiplierPairs D A N,
    ‖∑ b : Fin B, χ.chi (((M+(p.2.val : ℤ)) : ℤ) +
      ((p.1.val+1 : ℕ) : ZMod D)*(b.val : ZMod D))‖

lemma lemma32_actual_burgess_shift_absolute_weighted {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (M : ℤ) (A N B : ℕ) :
    lemma32BurgessShiftAbsoluteSum χ M A N B =
      ∑ x : ZMod D, (lemma32BurgessMultiplicity D M A N x : ℝ)*
        ‖lemma32ResidueShortSum χ B x‖ := by
  rw [lemma32_actual_burgess_multiplicity_weighted_sum]
  unfold lemma32BurgessShiftAbsoluteSum
  apply Finset.sum_congr rfl
  intro p hp
  have ha : (p.1.val+1).Coprime D := by
    have hm : p.1 ∈ lemma32BurgessUnitMultipliers D A :=
      (Finset.mem_product.mp hp).1
    exact (Finset.mem_filter.mp hm).2
  exact lemma32_actual_burgess_shift_short_sum_norm χ (p.1.val+1) ha B _

lemma lemma32_actual_burgess_amplification_fourth_bound {D A N B : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (hsize : 2*A*N < D)
    (hAN : A ≤ N) (hA : 1 ≤ A) (M : ℤ) :
    (lemma32BurgessShiftAbsoluteSum χ M A N B)^4 ≤
      ((A : ℝ)*(N : ℝ))^2 *
      (3*(A : ℝ)*(N : ℝ)*(1+Real.log (A : ℝ))) *
      (3*(D : ℝ)*(B : ℝ)^2 + lemma32UniformMomentConstant*
        Real.exp ((17/32)*Real.log (D : ℝ))*(B : ℝ)^4) := by
  rw [lemma32_actual_burgess_shift_absolute_weighted]
  have hw := lemma32_actual_weighted_burgess_moment χ B
    (lemma32BurgessMultiplicity D M A N)
  have hm : (∑ x : ZMod D, (lemma32BurgessMultiplicity D M A N x : ℝ)) ≤
      (A : ℝ)*(N : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast lemma32_actual_burgess_multiplicity_mass_bound M A N
  have hm0 : (0 : ℝ) ≤ ∑ x : ZMod D,
      (lemma32BurgessMultiplicity D M A N x : ℝ) :=
    Finset.sum_nonneg (fun x hx => Nat.cast_nonneg _)
  have hE := lemma32_actual_burgess_multiplicity_energy_log_bound hsize hAN hA M
  have hQ := lemma32_actual_uniform_burgess_fourth_moment χ B
  have hE0 : (0 : ℝ) ≤ ∑ x : ZMod D,
      (lemma32BurgessMultiplicity D M A N x : ℝ)^2 :=
    Finset.sum_nonneg (fun x hx => sq_nonneg _)
  have hQ0 : 0 ≤ lemma32BurgessFourthMoment χ B :=
    Finset.sum_nonneg (fun x hx => by positivity)
  calc
    _ ≤ _ := hw
    _ ≤ _ := mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ hm0 hm 2) hE hE0 (sq_nonneg _))
      hQ hQ0 (mul_nonneg (sq_nonneg _) (hE0.trans hE))

end ZhangLS.Spec
