import ZhangLS.Spec.Lemma23Nu20Bounds
import ZhangLS.Spec.DivisorCharacterSumNonnegative
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ComplexOrder
set_option maxHeartbeats 2000000

example {a b c d : ℂ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    a*c ≤ b*d := mul_le_mul hab hcd hc (ha.trans hab)

lemma lemma31_actual_nu_eq_zetaMul {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma23NuArithmeticFunction χ = χ.chi.zetaMul := by
  rfl

lemma lemma31_actual_nu_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    (0 : ℂ) ≤ lemma23NuArithmeticFunction χ n := by
  rw [lemma31_actual_nu_eq_zetaMul]
  exact DirichletCharacter.zetaMul_nonneg χ.quadratic n

lemma lemma31_actual_nu_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (k : ℕ) :
    lemma23NuArithmeticFunction χ (p^k) = ∑ j ∈ Finset.range (k+1), χ.evalNat p^j := by
  rw [lemma31_actual_nu_eq_zetaMul]
  rw [DirichletCharacter.zetaMul,ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  simp only [toArithmeticFunction,ArithmeticFunction.coe_mk,pow_eq_zero_iff',
    hp.ne_zero,ne_eq,false_and,↓reduceIte,RealPrimitiveCharacter.evalNat,Nat.cast_pow,map_pow]


lemma lemma31_actual_nu_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ArithmeticFunction.IsMultiplicative (lemma23NuArithmeticFunction χ) := by
  rw [lemma31_actual_nu_eq_zetaMul]
  exact χ.chi.isMultiplicative_zetaMul

lemma lemma31_actual_nu_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma23NuArithmeticFunction χ 1 = 1 := (lemma31_actual_nu_multiplicative χ).map_one

lemma lemma31_actual_nu_le_convolution_square {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma23NuArithmeticFunction χ n ≤
      (lemma23NuArithmeticFunction χ * lemma23NuArithmeticFunction χ) n := by
  by_cases hn : n = 0
  · subst n; simp
  · have hm : (1,n) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨by simp,hn⟩
    calc
      _ = lemma23NuArithmeticFunction χ 1 * lemma23NuArithmeticFunction χ n := by
        rw [lemma31_actual_nu_one,one_mul]
      _ ≤ ∑ q ∈ n.divisorsAntidiagonal,
        lemma23NuArithmeticFunction χ q.1 * lemma23NuArithmeticFunction χ q.2 :=
        Finset.single_le_sum (fun q _ => mul_nonneg
          (lemma31_actual_nu_nonneg χ q.1) (lemma31_actual_nu_nonneg χ q.2)) hm
      _ = _ := ArithmeticFunction.mul_apply.symm

end ZhangLS.Spec
