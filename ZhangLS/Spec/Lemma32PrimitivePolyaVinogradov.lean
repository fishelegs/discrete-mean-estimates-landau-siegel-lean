import ZhangLS.Spec.Lemma32FourierKernelSummatory
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma32_actual_primitive_polya_vinogradov {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (hD : 1<D) (M : ℤ) (N : ℕ) :
    ‖lemma32BurgessIntervalSum χ M N‖ ≤
      2*Real.sqrt (D : ℝ)*(1+Real.log (D : ℝ)) := by
  have hc := (lemma32_actual_interval_fourier_completion_norm χ hD M N).trans
    (mul_le_mul_of_nonneg_left (lemma32_fourier_interval_kernel_summatory M N)
      (Real.sqrt_nonneg (D : ℝ)))
  have he : Real.sqrt (D : ℝ)*(2*(D : ℝ)*(1+Real.log (D : ℝ))) =
      (D : ℝ)*(2*Real.sqrt (D : ℝ)*(1+Real.log (D : ℝ))) := by ring
  rw [he] at hc
  exact (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr χ.modulus_pos)).mp hc

lemma lemma32_actual_character_interval_trivial {D : ℕ} (χ : RealPrimitiveCharacter D)
    (M : ℤ) (N : ℕ) : ‖lemma32BurgessIntervalSum χ M N‖ ≤ (N : ℝ) := by
  unfold lemma32BurgessIntervalSum
  calc
    _ ≤ ∑ n : Fin N, ‖χ.chi (((M+(n.val : ℤ)) : ℤ) : ZMod D)‖ := norm_sum_le _ _
    _ ≤ ∑ _n : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun n hn => χ.chi.norm_le_one _)
    _ = _ := by simp

end ZhangLS.Spec
