import ZhangLS.Spec.Lemma31CharacterAbel
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
set_option maxHeartbeats 2000000

noncomputable def lemma31CharacterKernel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t : ℝ) : ℂ := ((t : ℂ)^2)⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n

lemma lemma31_character_kernel_eq_abel {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) :
    lemma31CharacterKernel χ t =
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ)^(-(1+1 : ℂ)) := by
  unfold lemma31CharacterKernel
  norm_num only [show (1+1 : ℂ) = 2 by norm_num]
  rw [Complex.cpow_neg,Complex.cpow_two,mul_comm]

lemma lemma31_character_kernel_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) : IntegrableOn (lemma31CharacterKernel χ) (Set.Ioi (1 : ℝ)) := by
  have hi := χ.abelIntegrand_integrable hD (show (0 : ℝ) < (1 : ℂ).re by norm_num)
  exact hi.congr_fun (fun t _ => (lemma31_character_kernel_eq_abel χ t).symm) measurableSet_Ioi

lemma lemma31_character_kernel_LAtOne {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    dirichletLFunction χ 1 = ∫ t : ℝ in Set.Ioi (1 : ℝ), lemma31CharacterKernel χ t := by
  rw [dirichletLFunction_eq_abelIntegral_of_pos_re χ hD (by norm_num),one_mul]
  unfold characterAbelIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (lemma31_character_kernel_eq_abel χ t).symm

lemma lemma31_character_kernel_norm_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (t : ℝ) (ht : 0 < t) :
    ‖lemma31CharacterKernel χ t‖ ≤ (D : ℝ) * t^(-2 : ℝ) := by
  unfold lemma31CharacterKernel
  rw [norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  rw [Real.rpow_neg ht.le,Real.rpow_two]
  calc
    _ ≤ (t^2)⁻¹ * (D : ℝ) :=
      mul_le_mul_of_nonneg_left (χ.norm_sum_Icc_evalNat_le_modulus hD ⌊t⌋₊) (by positivity)
    _ = _ := by ring

lemma lemma31_character_kernel_tail_norm_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (T : ℝ) (hT : 1 ≤ T) :
    ‖∫ t : ℝ in Set.Ioi T, lemma31CharacterKernel χ t‖ ≤ (D : ℝ) / T := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hi := (lemma31_character_kernel_integrable χ hD).mono_set
    (show Set.Ioi T ⊆ Set.Ioi (1 : ℝ) by intro t ht; exact lt_of_le_of_lt hT ht)
  have hm : IntegrableOn (fun t : ℝ => (D : ℝ) * t^(-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hTpos).const_mul _
  calc
    _ ≤ ∫ t : ℝ in Set.Ioi T, ‖lemma31CharacterKernel χ t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Set.Ioi T, (D : ℝ) * t^(-2 : ℝ) := by
      apply integral_mono_ae hi.norm hm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact lemma31_character_kernel_norm_le χ hD t (lt_trans hTpos ht)
    _ = (D : ℝ) / T := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hTpos]
      norm_num
      rw [Real.rpow_neg_one,div_eq_mul_inv]

end ZhangLS.Spec
