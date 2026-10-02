import ZhangLS.Spec.Lemma32AbelSquareRootBound
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_burgess_scale_half_power (C L : ℝ) (hC : 0 ≤ C) :
    (C*Real.exp ((25/128)*L))^(1/2 : ℝ) =
      C^(1/2 : ℝ)*Real.exp ((25/256)*L) := by
  rw [Real.mul_rpow hC (Real.exp_pos _).le,
    Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  congr 2
  ring

lemma lemma32_actual_L_bound_of_burgess_partial_sums {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (C : ℝ) (hC : 1 ≤ C)
    (hS : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, χ.evalNat n‖ ≤
      (C*Real.exp ((25/128)*lemma23PaperL D))*(N : ℝ)^(1/2 : ℝ))
    (s : ℂ) (hs : s.re = 3/4) :
    ‖dirichletLFunction χ s‖ ≤
      (8*C^(1/2 : ℝ))*Real.exp ((25/256)*lemma23PaperL D)*‖s‖ := by
  have hL : 0 ≤ lemma23PaperL D := Real.log_nonneg (by exact_mod_cast hD.le)
  have he : 1 ≤ Real.exp ((25/128)*lemma23PaperL D) := by
    calc
      _ = Real.exp 0 := Real.exp_zero.symm
      _ ≤ _ := Real.exp_le_exp.mpr (by positivity)
  have hB : 1 ≤ C*Real.exp ((25/128)*lemma23PaperL D) := one_le_mul_of_one_le_of_one_le hC he
  have h := lemma32_actual_L_bound_of_square_root_partial_sums χ hD
    (C*Real.exp ((25/128)*lemma23PaperL D)) hB hS s hs
  rw [lemma32_burgess_scale_half_power C (lemma23PaperL D) (by linarith)] at h
  convert h using 1 <;> ring

end ZhangLS.Spec
