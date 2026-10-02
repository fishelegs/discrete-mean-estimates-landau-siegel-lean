import ZhangLS.Spec.Lemma162OddLocalRatio
import ZhangLS.Spec.Lemma162OddCoefficientNorm
import ZhangLS.Spec.Lemma162CoefficientReassembly
import ZhangLS.Spec.Lemma162CubicNormSeries

/-! Actual cubic coefficient estimates. Every analytic bound below is
obtained from the verified local M-ratio formulas and the original kernels.
The odd-prime constant may depend on χ, β and γ; this suffices for absolute
convergence and is not a uniform continuation-strip estimate. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_lambda_prime_power_norm {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime) (i : ℕ) :
    ‖lemma161Lambda χ β (p^i)‖ ≤ 5 := by
  cases i with
  | zero => simp
  | succ i =>
    have he : lemma161Lambda χ β (p^(i+1)) = lemma161LambdaFactor χ β p 1 := by
      simp [lemma161Lambda,Nat.primeFactors_prime_pow (Nat.succ_ne_zero i) hp]
    rw [he]
    exact lemma161_lambda_norm_le χ β hβ hp

lemma lemma162_prime_power_varpi_weight_norm {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re = 0)
    (γ : ℂ) (hγ : γ.re = 0) (hp : p.Prime) (i j : ℕ) :
    ‖lemma161Lambda χ β (p^i)*((p^i:ℕ):ℂ)^γ*χ.evalNat (p^j)‖ ≤ 5 := by
  have hpw : ‖((p^i:ℕ):ℂ)^γ‖ = 1 := by
    simpa only [neg_neg] using lemma83_cpow_shift_norm (pow_pos hp.pos i) (-γ)
      (by simp [hγ])
  simp only [norm_mul,hpw,mul_one]
  calc
    _ ≤ (5:ℝ)*1 := mul_le_mul (lemma162_lambda_prime_power_norm χ β hβ hp i)
      (χ.evalNat_norm_le_one _) (norm_nonneg _) (by norm_num)
    _ = 5 := by norm_num

lemma lemma162_actual_odd_kernel_prime_power_norm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re = 0)
    (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0)
    (q : Nat.Primes) (hq : 2<q.val) (i j : ℕ) (K : ℝ)
    (hK : ‖(lemma161PrimeFactor χ β q (1-γ))⁻¹‖ ≤ K) :
    ‖lemma162OddVarpiKernel χ β γ (q.val^i) (q.val^j)‖ ≤
      5*lemma162GeneralMNormBound*K := by
  have hs : 9/10 ≤ (1-γ).re := by simp [hγ]; norm_num
  have hr : ‖lemma162OddMEulerProduct χ β (q.val^i) (q.val^j) (1-γ)/
      lemma162OddMEulerProduct χ β 1 1 (1-γ)‖ ≤ lemma162GeneralMNormBound*K := by
    rw [lemma162_odd_m_prime_power_ratio χ β hβ q hq i j (1-γ) hs hB,
      norm_div,div_eq_mul_inv,← norm_inv]
    exact mul_le_mul (lemma162_general_m_local_norm χ β hβ _ _ q (1-γ) hs)
      hK (norm_nonneg _) lemma162_general_m_norm_bound_pos.le
  rw [lemma162OddVarpiKernel,norm_mul]
  calc
    _ ≤ (5:ℝ)*(lemma162GeneralMNormBound*K) :=
      mul_le_mul (lemma162_prime_power_varpi_weight_norm χ β hβ γ hγ q.property i j)
        hr (norm_nonneg _) (by norm_num)
    _ = 5*lemma162GeneralMNormBound*K := by ring

/-- Actual uniform-in-prime cubic bound, with a parameter-dependent constant. -/
lemma lemma162_actual_odd_coefficient_cubic_bound {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re = 0)
    (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      ‖lemma162OddCoefficientArithmetic χ β γ (p^r)‖ ≤ C*((r:ℝ)+1)^3 := by
  have hs : 9/10 ≤ (1-γ).re := by simp [hγ]; norm_num
  obtain ⟨K,hK,hKi⟩ := lemma162_odd_inverse_family_bounded χ β hβ (1-γ) hs
  let C : ℝ := max 1 (5*lemma162GeneralMNormBound*K)
  have hC : 0<C := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro p hp r
  by_cases hodd : 2<p
  · apply lemma162_odd_coefficient_prime_power_norm_of_kernel χ β γ hp r C hC.le
    intro j hj
    exact (lemma162_actual_odd_kernel_prime_power_norm χ β hβ γ hγ hB
      ⟨p,hp⟩ hodd j (r-j) K (hKi ⟨p,hp⟩ hodd)).trans (le_max_right _ _)
  · have hp2 : p=2 := by have := hp.two_le; omega
    subst p
    cases r with
    | zero =>
      have hone := (lemma162_odd_coefficient_multiplicative χ β hβ γ hγ hB).map_one
      simp only [pow_zero,hone,norm_one,Nat.cast_zero,zero_add,one_pow,mul_one]
      exact le_max_left _ _
    | succ r =>
      have hn : ¬((2:ℕ)^(r+1)).Coprime 2 := by
        rw [Nat.coprime_pow_left_iff (Nat.succ_pos r)]
        norm_num
      change ‖if ((2:ℕ)^(r+1)).Coprime 2 then _ else (0:ℂ)‖ ≤ _
      rw [if_neg hn,norm_zero]
      positivity

noncomputable def lemma162TwoNormConstant {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) : ℝ :=
  5*lemma162GeneralMNormBound*‖(lemma162TwoNormalizer χ β (1-γ))⁻¹‖

lemma lemma162_two_norm_constant_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) : 0 ≤ lemma162TwoNormConstant χ β γ := by
  have hM := lemma162_general_m_norm_bound_pos
  unfold lemma162TwoNormConstant
  positivity

lemma lemma162_actual_two_kernel_prime_power_norm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re = 0)
    (γ : ℂ) (hγ : γ.re = 0) (i j : ℕ) :
    ‖lemma162TwoVarpiKernel χ β γ (2^i) (2^j)‖ ≤
      lemma162TwoNormConstant χ β γ := by
  have hs : 9/10 ≤ (1-γ).re := by simp [hγ]; norm_num
  have hr : ‖lemma162GeneralMPrimeFactor χ β (2^i) (2^j) lemma162PrimeTwo (1-γ)/
      lemma162TwoNormalizer χ β (1-γ)‖ ≤ lemma162GeneralMNormBound*
        ‖(lemma162TwoNormalizer χ β (1-γ))⁻¹‖ := by
    rw [norm_div,div_eq_mul_inv,← norm_inv]
    exact mul_le_mul_of_nonneg_right
      (lemma162_general_m_local_norm χ β hβ _ _ lemma162PrimeTwo (1-γ) hs)
      (norm_nonneg _)
  rw [lemma162TwoVarpiKernel,norm_mul]
  calc
    _ ≤ (5:ℝ)*(lemma162GeneralMNormBound*‖(lemma162TwoNormalizer χ β (1-γ))⁻¹‖) :=
      mul_le_mul (lemma162_prime_power_varpi_weight_norm χ β hβ γ hγ Nat.prime_two i j)
        hr (norm_nonneg _) (by norm_num)
    _ = lemma162TwoNormConstant χ β γ := by unfold lemma162TwoNormConstant; ring

/-- The actual sparse 2-adic coefficient, including r=0, has cubic growth.
No unit or nonzero degree-zero coefficient is assumed. -/
lemma lemma162_actual_two_coefficient_prime_power_norm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re = 0)
    (γ : ℂ) (hγ : γ.re = 0) (r : ℕ) :
    ‖lemma162TwoCoefficientArithmetic χ β γ (2^r)‖ ≤
      lemma162TwoNormConstant χ β γ*((r:ℝ)+1)^3 := by
  have hv := lemma162_divisor_kernel_prime_power_norm (lemma162TwoVarpiKernel χ β γ)
    Nat.prime_two r (lemma162TwoNormConstant χ β γ)
    (fun j hj => lemma162_actual_two_kernel_prime_power_norm χ β hβ γ hγ j (r-j))
  have hn := lemma162_actual_nu_chi_prime_power_norm χ Nat.prime_two r
  simp only [lemma162TwoCoefficientArithmetic,ArithmeticFunction.pmul_apply,
    lemma162_prime_power_part_apply,norm_mul]
  calc
    _ ≤ (lemma162TwoNormConstant χ β γ*((r:ℝ)+1))*((r:ℝ)+1)^2 :=
      mul_le_mul hv hn (norm_nonneg _) (mul_nonneg (lemma162_two_norm_constant_nonneg χ β γ)
        (by positivity))
    _ = lemma162TwoNormConstant χ β γ*((r:ℝ)+1)^3 := by ring

lemma lemma162_actual_two_local_norm_series {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re = 0)
    (γ : ℂ) (hγ : γ.re = 0) (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    Summable (fun r : ℕ => ‖lemma162TwoCoefficientArithmetic χ β γ (2^r)*z^r‖) ∧
      (∑' r : ℕ, ‖lemma162TwoCoefficientArithmetic χ β γ (2^r)*z^r‖) ≤
        ‖lemma162TwoCoefficientArithmetic χ β γ 1‖+
          (lemma162TwoNormConstant χ β γ*lemma162CubicNormConstant)*‖z‖ := by
  apply lemma162_cubic_local_norm_series_general
    (fun r => lemma162TwoCoefficientArithmetic χ β γ (2^r))
    (lemma162TwoNormConstant χ β γ) (lemma162_two_norm_constant_nonneg χ β γ)
    (fun r => ?_) z hz
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
    lemma162_actual_two_coefficient_prime_power_norm χ β hβ γ hγ (r+1)

/-- All true odd local norm series admit one summable Euler majorant.
The constant is independent of p and z, but may depend on the parameters. -/
lemma lemma162_actual_odd_local_norm_series {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re = 0)
    (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, p.Prime → ∀ z : ℂ, ‖z‖ ≤ 1/2 →
      Summable (fun r : ℕ => ‖lemma162OddCoefficientArithmetic χ β γ (p^r)*z^r‖) ∧
        (∑' r : ℕ, ‖lemma162OddCoefficientArithmetic χ β γ (p^r)*z^r‖) ≤
          1+C*‖z‖ := by
  obtain ⟨C,hC,hbound⟩ := lemma162_actual_odd_coefficient_cubic_bound χ β hβ γ hγ hB
  refine ⟨C*lemma162CubicNormConstant,
    mul_nonneg hC.le lemma162_cubic_norm_constant_nonneg,?_⟩
  intro p hp z hz
  apply lemma162_cubic_local_norm_series
    (fun r => lemma162OddCoefficientArithmetic χ β γ (p^r)) C hC.le
    (by simpa only [pow_zero] using
      (lemma162_odd_coefficient_multiplicative χ β hβ γ hγ hB).map_one)
    (fun r => ?_) z hz
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hbound p hp (r+1)

end ZhangLS.Spec
