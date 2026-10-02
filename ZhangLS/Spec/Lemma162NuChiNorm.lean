import ZhangLS.Spec.Lemma162NuChi

/-! Norm estimates for the actual arithmetic convolution ν * χ.
This file does not replace ν * χ by a model local sequence. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma162_character_arithmetic_norm_le_one {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23CharacterArithmeticFunction χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [lemma161_character_arithmetic_eq χ hn]
    exact χ.evalNat_norm_le_one n

lemma lemma162_actual_nu_prime_power_norm {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (r : ℕ) :
    ‖lemma23NuArithmeticFunction χ (p^r)‖ ≤ (r:ℝ)+1 := by
  rw [lemma31_actual_nu_prime_power χ hp r]
  calc
    ‖∑ j ∈ range (r+1), χ.evalNat p^j‖ ≤
        ∑ j ∈ range (r+1), ‖χ.evalNat p^j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range (r+1), (1:ℝ) := by
      apply sum_le_sum
      intro j hj
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (χ.evalNat_norm_le_one p)
    _ = (r:ℝ)+1 := by simp

/-- The true multiplier has quadratic prime-power growth. -/
lemma lemma162_actual_nu_chi_prime_power_norm {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (r : ℕ) :
    ‖lemma162NuChi χ (p^r)‖ ≤ ((r:ℝ)+1)^2 := by
  rw [lemma162NuChi,ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      lemma23NuArithmeticFunction χ a * lemma23CharacterArithmeticFunction χ b),
    Nat.sum_divisors_prime_pow hp]
  calc
    ‖∑ j ∈ range (r+1), lemma23NuArithmeticFunction χ (p^j) *
        lemma23CharacterArithmeticFunction χ (p^r / p^j)‖ ≤
        ∑ j ∈ range (r+1), ‖lemma23NuArithmeticFunction χ (p^j) *
          lemma23CharacterArithmeticFunction χ (p^r / p^j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range (r+1), ((r:ℝ)+1) := by
      apply sum_le_sum
      intro j hj
      have hjr : j ≤ r := Nat.le_of_lt_succ (mem_range.mp hj)
      have hjr' : (j:ℝ) ≤ (r:ℝ) := by exact_mod_cast hjr
      have hn : ‖lemma23NuArithmeticFunction χ (p^j)‖ ≤ (r:ℝ)+1 :=
        (lemma162_actual_nu_prime_power_norm χ hp j).trans (by linarith)
      rw [norm_mul]
      calc
        _ ≤ ((r:ℝ)+1)*1 := mul_le_mul hn
          (lemma162_character_arithmetic_norm_le_one χ _) (norm_nonneg _) (by positivity)
        _ = (r:ℝ)+1 := mul_one _
    _ = ((r:ℝ)+1)^2 := by simp; ring

end ZhangLS.Spec
