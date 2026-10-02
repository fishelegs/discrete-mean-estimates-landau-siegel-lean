import ZhangLS.Spec.Lemma32LeftIntegralBound
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_burgess_scale_fourth_decay (C L : ℝ) :
    (C*Real.exp ((25/128)*L))^4*Real.exp (-(127/128)*L) =
      C^4*Real.exp (-(27/128)*L) := by
  have he : (Real.exp ((25/128)*L))^4 = Real.exp ((25/32)*L) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [mul_pow,he,mul_assoc,← Real.exp_add]
  congr 2
  ring

lemma lemma32_actual_left_integral_bound_of_burgess_partial_sums {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (C : ℝ) (hC : 1 ≤ C)
    (hS : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, χ.evalNat n‖ ≤
      (C*Real.exp ((25/128)*lemma23PaperL D))*(N : ℝ)^(1/2 : ℝ)) :
    ‖lemma32LeftVerticalIntegral χ‖ ≤
      lemma32LeftErrorConstant*C^4*Real.exp (-(27/128)*lemma23PaperL D) := by
  have hL : 0 ≤ lemma23PaperL D := Real.log_nonneg (by exact_mod_cast hD.le)
  have he : 1 ≤ Real.exp ((25/128)*lemma23PaperL D) := by
    calc
      _ = Real.exp 0 := Real.exp_zero.symm
      _ ≤ _ := Real.exp_le_exp.mpr (by positivity)
  have hB : 1 ≤ C*Real.exp ((25/128)*lemma23PaperL D) := one_le_mul_of_one_le_of_one_le hC he
  have h := lemma32_actual_left_integral_bound_of_partial_sums χ hD
    (C*Real.exp ((25/128)*lemma23PaperL D)) hB hS
  rw [mul_assoc,lemma32_burgess_scale_fourth_decay C (lemma23PaperL D)] at h
  convert h using 1 <;> ring

end ZhangLS.Spec
