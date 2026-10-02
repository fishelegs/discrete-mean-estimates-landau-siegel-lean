import ZhangLS.Spec.Lemma162OddVarpi
import ZhangLS.Spec.Lemma162NuChiNorm

/-! Finite norm bounds for the true odd coefficient sequence. Analytic input
is confined to the explicit norm hypothesis for the genuine normalized
M(d,l)-kernel; no model coefficients or prime-factor definition is substituted. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma162_divisor_kernel_prime_power_norm (H : ℕ → ℕ → ℂ)
    {p : ℕ} (hp : p.Prime) (r : ℕ) (C : ℝ)
    (hH : ∀ j : ℕ, j ≤ r → ‖H (p^j) (p^(r-j))‖ ≤ C) :
    ‖lemma152DivisorKernelSum H (p^r)‖ ≤ C*((r:ℝ)+1) := by
  change ‖∑ dl ∈ (p^r).divisorsAntidiagonal, H dl.1 dl.2‖ ≤ _
  rw [Nat.sum_divisorsAntidiagonal H,Nat.sum_divisors_prime_pow hp]
  calc
    ‖∑ j ∈ range (r+1), H (p^j) (p^r / p^j)‖ ≤
        ∑ j ∈ range (r+1), ‖H (p^j) (p^r / p^j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range (r+1), C := by
      apply sum_le_sum
      intro j hj
      have hjr : j ≤ r := Nat.le_of_lt_succ (mem_range.mp hj)
      rw [Nat.pow_div hjr hp.pos]
      exact hH j hjr
    _ = C*((r:ℝ)+1) := by simp; ring

/-- The exact odd arithmetic coefficient has cubic growth as soon as its
true normalized prime-power kernels are uniformly bounded. -/
lemma lemma162_odd_coefficient_prime_power_norm_of_kernel {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (β γ : ℂ) (hp : p.Prime) (r : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ j : ℕ, j ≤ r →
      ‖lemma162OddVarpiKernel χ β γ (p^j) (p^(r-j))‖ ≤ C) :
    ‖lemma162OddCoefficientArithmetic χ β γ (p^r)‖ ≤ C*((r:ℝ)+1)^3 := by
  have hv : ‖lemma162OddVarpiArithmetic χ β γ (p^r)‖ ≤ C*((r:ℝ)+1) :=
    lemma162_divisor_kernel_prime_power_norm (lemma162OddVarpiKernel χ β γ) hp r C hH
  have hn := lemma162_actual_nu_chi_prime_power_norm χ hp r
  change ‖if (p^r).Coprime 2 then
    lemma162OddVarpiArithmetic χ β γ (p^r)*lemma162NuChi χ (p^r) else 0‖ ≤ _
  by_cases ho : (p^r).Coprime 2
  · rw [if_pos ho,norm_mul]
    calc
      _ ≤ (C*((r:ℝ)+1))*((r:ℝ)+1)^2 :=
        mul_le_mul hv hn (norm_nonneg _) (by positivity)
      _ = C*((r:ℝ)+1)^3 := by ring
  · rw [if_neg ho,norm_zero]
    positivity

end ZhangLS.Spec
