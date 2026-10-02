import ZhangLS.Spec.Lemma31OrderedArithmetic
import ZhangLS.Spec.Lemma83Definitions

/-! Actual Appendix B arithmetic. No asymptotic estimate or contour shift is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Finset ArithmeticFunction Complex
open scoped ArithmeticFunction.zeta Classical

/-- Pointwise multiplication by the actual n^β, preserving the zero convention. -/
noncomputable def lemma151Twist (β : ℂ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => (n : ℂ)^β * f n, by simp⟩

lemma lemma151_twist_mul (β : ℂ) (f g : ArithmeticFunction ℂ) :
    lemma151Twist β (f*g) = lemma151Twist β f * lemma151Twist β g := by
  ext n
  simp only [lemma151Twist, ArithmeticFunction.coe_mk, ArithmeticFunction.mul_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he := (Nat.mem_divisorsAntidiagonal.mp ha).1
  rw [← he, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

lemma lemma151_mu_mul_actual_nu {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) * lemma23NuArithmeticFunction χ =
      lemma23CharacterArithmeticFunction χ := by
  rw [lemma23NuArithmeticFunction, ← mul_assoc,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]

/-- ρ_j(n)=∑_{d|n} μ(d)d^β, with genuine Möbius. -/
noncomputable def lemma151Rho (β : ℂ) : ArithmeticFunction ℂ :=
  (ζ : ArithmeticFunction ℂ) * lemma151Twist β ArithmeticFunction.moebius

/-- ρ*_j(n)=∑_{d|n} χ(d)d^β, with the actual real primitive character. -/
noncomputable def lemma151RhoStar {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) : ArithmeticFunction ℂ :=
  (ζ : ArithmeticFunction ℂ) * lemma151Twist β (lemma23CharacterArithmeticFunction χ)

lemma lemma151_rho_divisor_sum (β : ℂ) (n : ℕ) :
    lemma151Rho β n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)*(d : ℂ)^β := by
  simp only [lemma151Rho, ArithmeticFunction.coe_zeta_mul_apply,
    lemma151Twist, ArithmeticFunction.coe_mk, ArithmeticFunction.intCoe_apply, mul_comm]

lemma lemma151_rhostar_divisor_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (n : ℕ) :
    lemma151RhoStar χ β n = ∑ d ∈ n.divisors, χ.evalNat d*(d : ℂ)^β := by
  simp only [lemma151RhoStar, ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  simp [lemma151Twist, lemma23CharacterArithmeticFunction, toArithmeticFunction, hd0,
    RealPrimitiveCharacter.evalNat, mul_comm]

/-- Exact arithmetic source of the B.1 replacement; the ν term is not a free majorant. -/
theorem lemma151_rhostar_actual_nu_convolution {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) :
    lemma151RhoStar χ β = lemma151Rho β * lemma151Twist β (lemma23NuArithmeticFunction χ) := by
  unfold lemma151RhoStar lemma151Rho
  rw [mul_assoc, ← lemma151_twist_mul, lemma151_mu_mul_actual_nu]

lemma lemma151_moebius_norm_le_one (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

lemma lemma151_power_norm {β : ℂ} (hβ : β.re = 0) {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℂ)^β‖ = 1 := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn), hβ,
    Real.rpow_zero]

/-- The elementary absolute divisor-count bound, with no O-constant. -/
theorem lemma151_rho_norm_le_tau {β : ℂ} (hβ : β.re = 0) (n : ℕ) :
    ‖lemma151Rho β n‖ ≤ (n.divisors.card : ℝ) := by
  rw [lemma151_rho_divisor_sum]
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖(ArithmeticFunction.moebius d : ℂ)*(d : ℂ)^β‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, lemma151_power_norm hβ (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)), mul_one]
      exact lemma151_moebius_norm_le_one d
    _ = _ := by simp

/-- Exact error formula with the n=1 contribution removed by the arithmetic unit. -/
theorem lemma151_rhostar_sub_rho_exact {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (n : ℕ) :
    lemma151RhoStar χ β n - lemma151Rho β n =
      ∑ a ∈ n.divisorsAntidiagonal,
        lemma151Rho β a.1 *
          ((a.2 : ℂ)^β * lemma23NuArithmeticFunction χ a.2 -
            (if a.2 = 1 then 1 else 0)) := by
  rw [lemma151_rhostar_actual_nu_convolution]
  have he : lemma151Rho β * lemma151Twist β (lemma23NuArithmeticFunction χ) - lemma151Rho β =
      lemma151Rho β * (lemma151Twist β (lemma23NuArithmeticFunction χ) - 1) := by
    rw [mul_sub, mul_one]
  change (lemma151Rho β * lemma151Twist β (lemma23NuArithmeticFunction χ) - lemma151Rho β) n = _
  rw [he, ArithmeticFunction.mul_apply]
  rfl

/-- B.1's pointwise arithmetic bound, retaining all genuine ν coefficients and no
unstated asymptotic. This finite inequality is valid before invoking Lemma 3.2. -/
theorem lemma151_rhostar_sub_rho_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    {β : ℂ} (hβ : β.re = 0) (n : ℕ) :
    ‖lemma151RhoStar χ β n - lemma151Rho β n‖ ≤
      ∑ a ∈ n.divisorsAntidiagonal,
        if a.2 = 1 then 0 else (a.1.divisors.card : ℝ) * ‖lemma23NuArithmeticFunction χ a.2‖ := by
  rw [lemma151_rhostar_sub_rho_exact]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  by_cases h1 : a.2 = 1
  · simp [h1, lemma31_actual_nu_one]
  · have ha0 : a.2 ≠ 0 := by
      intro hz
      have he := (Nat.mem_divisorsAntidiagonal.mp ha)
      simp [hz] at he
      exact he.2 he.1.symm
    simp only [if_neg h1, sub_zero, norm_mul, lemma151_power_norm hβ ha0, one_mul]
    exact mul_le_mul_of_nonneg_right (lemma151_rho_norm_le_tau hβ _) (norm_nonneg _)

end ZhangLS.Spec
