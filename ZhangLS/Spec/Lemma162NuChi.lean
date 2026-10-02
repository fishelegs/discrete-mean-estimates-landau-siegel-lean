import ZhangLS.Spec.Lemma162Definitions
import ZhangLS.Spec.Lemma31OrderedArithmetic

/-! The Hadamard multiplier is the actual ν*χ arithmetic convolution,
not a guessed local weight. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

@[simp] lemma lemma162_character_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma23CharacterArithmeticFunction χ 1 = 1 := by
  simp [lemma23CharacterArithmeticFunction,toArithmeticFunction]

@[simp] lemma lemma162_nu_chi_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma162NuChi χ 1 = 1 := by
  simp [lemma162NuChi,ArithmeticFunction.mul_apply,lemma31_actual_nu_one]

/-- The factor 1+2χ(q) is exact at every prime, including ramified primes. -/
lemma lemma162_nu_chi_prime {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime) :
    lemma162NuChi χ p = 1+2*χ.evalNat p := by
  have hn : lemma23NuArithmeticFunction χ p = 1+χ.evalNat p := by
    simpa [Finset.sum_range_succ] using lemma31_actual_nu_prime_power χ hp 1
  rw [lemma162NuChi,ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      lemma23NuArithmeticFunction χ a*lemma23CharacterArithmeticFunction χ b),
    hp.divisors,Finset.sum_pair (Ne.symm hp.ne_one)]
  rw [Nat.div_one,Nat.div_self hp.pos,hn,lemma31_actual_nu_one,lemma162_character_one,
    lemma161_character_arithmetic_eq χ hp.ne_zero]
  ring

/-- Actual source prime coefficient; all finite-D M-ratios are retained. -/
lemma lemma162_actual_hadamard_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (hp : p.Prime) :
    lemma162Coefficient χ β γ M p = (1+2*χ.evalNat p)*
      (χ.evalNat p*(M 1 p (1-γ)/lemma161Star χ β (1-γ)) +
        lemma161LambdaFactor χ β p 1*(p:ℂ)^γ*
          (M p 1 (1-γ)/lemma161Star χ β (1-γ))) := by
  rw [lemma162Coefficient,lemma162_varpi_prime χ β γ M hp,lemma162_nu_chi_prime χ hp]
  ring

end ZhangLS.Spec
