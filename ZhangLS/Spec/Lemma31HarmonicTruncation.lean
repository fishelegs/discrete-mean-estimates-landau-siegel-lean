import ZhangLS.Spec.Lemma31CharacterKernel
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
set_option maxHeartbeats 2000000

lemma lemma31_character_harmonic_truncation_identity {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * χ.evalNat n) - dirichletLFunction χ 1 =
      (N : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N, χ.evalNat n) -
        ∫ t : ℝ in Set.Ioi (N : ℝ), lemma31CharacterKernel χ t := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi := lemma31_character_kernel_integrable χ hD
  have hit := hi.mono_set
    (show Set.Ioi (N : ℝ) ⊆ Set.Ioi (1 : ℝ) by intro t ht; exact lt_of_le_of_lt hn ht)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  rw [intervalIntegral.integral_of_le hn] at hsplit
  rw [lemma31_character_harmonic_abel χ hD N hN,lemma31_character_kernel_LAtOne χ hD]
  change (N : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N, χ.evalNat n) +
      (∫ t : ℝ in Set.Ioc (1 : ℝ) N, lemma31CharacterKernel χ t) -
      (∫ t : ℝ in Set.Ioi (1 : ℝ), lemma31CharacterKernel χ t) = _
  rw [← hsplit]
  ring

lemma lemma31_character_harmonic_truncation_norm_le {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * χ.evalNat n) - dirichletLFunction χ 1‖ ≤
      2 * (D : ℝ) / N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [lemma31_character_harmonic_truncation_identity χ hD N hN]
  have he : ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N, χ.evalNat n)‖ ≤ (D : ℝ)/N := by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    calc
      _ ≤ (N : ℝ)⁻¹ * (D : ℝ) := mul_le_mul_of_nonneg_left
        (χ.norm_sum_Icc_evalNat_le_modulus hD N) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N, χ.evalNat n)‖ +
        ‖∫ t : ℝ in Set.Ioi (N : ℝ), lemma31CharacterKernel χ t‖ := norm_sub_le _ _
    _ ≤ (D : ℝ)/N + (D : ℝ)/N := add_le_add he
      (lemma31_character_kernel_tail_norm_le χ hD (N : ℝ) hn)
    _ = _ := by ring

lemma lemma31_character_harmonic_truncation_real_le {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (N : ℕ) (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ * (χ.evalNat n).re) - realLAtOne χ| ≤
      2 * (D : ℝ) / N := by
  have hn := lemma31_character_harmonic_truncation_norm_le χ hD N hN
  have hr := Complex.abs_re_le_norm
    ((∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * χ.evalNat n) - dirichletLFunction χ 1)
  have he : ((∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * χ.evalNat n) -
      dirichletLFunction χ 1).re =
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ * (χ.evalNat n).re) - realLAtOne χ := by
    simp [Complex.re_sum,Complex.mul_re,← Complex.ofReal_natCast,← Complex.ofReal_inv,
      realLAtOne,realLValue]
  rw [he] at hr
  exact hr.trans hn

end ZhangLS.Spec
