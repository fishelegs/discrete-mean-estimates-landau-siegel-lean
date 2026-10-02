import ZhangLS.Spec.Lemma32LeftIntegrandBound
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32LeftErrorConstant : ℝ :=
  (1/(2*Real.pi))*(2*(lemma32RamificationSavingConstant*lemma32RegularProductBound (3/4))*8^8)*
    lemma32LeftKernelConstant

lemma lemma32_left_error_constant_pos : 0 < lemma32LeftErrorConstant := by
  have hr := lemma32_ramification_saving_constant_pos
  have hp := lemma32_regular_product_bound_pos (3/4)
  have hk := lemma32_left_kernel_constant_pos
  unfold lemma32LeftErrorConstant
  positivity

lemma lemma32_actual_left_integral_bound_of_partial_sums {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (B : ℝ) (hB : 1 ≤ B)
    (hS : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, χ.evalNat n‖ ≤ B*(N : ℝ)^(1/2 : ℝ)) :
    ‖lemma32LeftVerticalIntegral χ‖ ≤
      lemma32LeftErrorConstant*B^4*Real.exp (-(127/128)*lemma23PaperL D) := by
  let A : ℝ := (2*(lemma32RamificationSavingConstant*lemma32RegularProductBound (3/4))*8^8*B^4)*
    Real.exp (-(127/128)*lemma23PaperL D)
  have hr := lemma32_ramification_saving_constant_pos
  have hp := lemma32_regular_product_bound_pos (3/4)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hf : Integrable (fun t : ℝ => lemma32CircleIntegrand χ (lemma32LeftLine t)) :=
    lemma32_actual_left_vertical_integrable χ hD (-1/4) (by norm_num) (by norm_num) (by norm_num)
  have hmaj : Integrable (fun t : ℝ => A*lemma32LeftKernel t) := lemma32_left_kernel_integrable.const_mul _
  have hi : ‖∫ t : ℝ, lemma32CircleIntegrand χ (lemma32LeftLine t)‖ ≤ A*lemma32LeftKernelConstant := by
    calc
      _ ≤ ∫ t : ℝ, ‖lemma32CircleIntegrand χ (lemma32LeftLine t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, A*lemma32LeftKernel t := by
        apply integral_mono_ae hf.norm hmaj
        filter_upwards [] with t
        exact lemma32_actual_left_integrand_bound_of_partial_sums χ hD B hB hS t
      _ = A*(∫ t : ℝ, lemma32LeftKernel t) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left lemma32_left_kernel_integral_le hA
  unfold lemma32LeftVerticalIntegral
  change ‖((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ,
    lemma32CircleIntegrand χ (lemma32LeftLine t))‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (1/(2*Real.pi) : ℝ))]
  calc
    _ ≤ (1/(2*Real.pi))*(A*lemma32LeftKernelConstant) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by unfold lemma32LeftErrorConstant A;ring

end ZhangLS.Spec
