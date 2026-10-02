import ZhangLS.Spec.Lemma32CoefficientMajorant
import ZhangLS.Spec.Lemma23GoodSet

/-!
# The actual product-tail coefficient majorant

The inverse coefficients have local values `1, -(1+χ(p)), χ(p), 0, ...`.
Their absolute convolution with `ν` is multiplicative and is bounded locally by
`ν(p^e) (e+1)`.  This preserves the small `ν` factor in the paper's estimate
`|varsigma(n)| ≤ ν(n) τ₂(n)`; the coarser divisor bound for `υ` is insufficient.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.Moebius Classical
set_option maxHeartbeats 2000000

noncomputable def lemma36NormArithmeticFunction
    (f : ArithmeticFunction ℂ) : ArithmeticFunction ℝ :=
  ⟨fun n => ‖f n‖, by simp⟩

@[simp] lemma lemma36_norm_arithmetic_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    lemma36NormArithmeticFunction f n = ‖f n‖ := rfl

lemma lemma36_norm_arithmetic_multiplicative (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) : (lemma36NormArithmeticFunction f).IsMultiplicative := by
  refine ⟨by simp [hf.map_one], ?_⟩
  intro m n hmn
  simp only [lemma36_norm_arithmetic_apply, hf.map_mul_of_coprime hmn, norm_mul]

lemma lemma36_upsilon_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (lemma23UpsilonArithmeticFunction χ).IsMultiplicative := by
  have he : lemma23CharacterMoebiusArithmeticFunction χ =
      (lemma23CharacterArithmeticFunction χ).pmul (μ : ArithmeticFunction ℂ) := by
    ext n
    by_cases hn : n = 0
    · subst n; simp
    · simp [lemma23CharacterMoebiusArithmeticFunction, lemma23CharacterArithmeticFunction,
        ArithmeticFunction.pmul_apply, toArithmeticFunction, hn]
  rw [lemma23UpsilonArithmeticFunction, he]
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (χ.chi.isMultiplicative_toArithmeticFunction.pmul
      ArithmeticFunction.isMultiplicative_moebius.intCast)

lemma lemma36_upsilon_prime_power_sum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (k : ℕ) :
    lemma23UpsilonArithmeticFunction χ (p^k) =
      ∑ j ∈ Finset.range (k+1), (μ (p^j) : ℂ) *
        (χ.evalNat p^(k-j) * (μ (p^(k-j)) : ℂ)) := by
  rw [lemma23UpsilonArithmeticFunction, ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.intCoe_apply]
  rw [
    Nat.sum_divisorsAntidiagonal (fun a b =>
      (μ a : ℂ) * lemma23CharacterMoebiusArithmeticFunction χ b),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.pow_div (show j ≤ k by have := Finset.mem_range.mp hj; omega) hp.pos]
  simp [lemma23CharacterMoebiusArithmeticFunction, toArithmeticFunction,
    hp.ne_zero, RealPrimitiveCharacter.evalNat]

lemma lemma36_upsilon_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) : lemma23UpsilonArithmeticFunction χ p = -(1+χ.evalNat p) := by
  have h := lemma36_upsilon_prime_power_sum χ hp 1
  simp only [pow_one] at h
  rw [h]
  simp [Finset.sum_range_succ, ArithmeticFunction.moebius_apply_prime hp]

lemma lemma36_upsilon_prime_square {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) : lemma23UpsilonArithmeticFunction χ (p^2) = χ.evalNat p := by
  rw [lemma36_upsilon_prime_power_sum χ hp 2]
  simp [Finset.sum_range_succ, ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime_pow hp]

lemma lemma36_upsilon_prime_power_ge_three {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (k : ℕ) :
    lemma23UpsilonArithmeticFunction χ (p^(k+3)) = 0 := by
  rw [lemma36_upsilon_prime_power_sum χ hp (k+3)]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hj2 : 2 ≤ j
  · have hμ : μ (p^j) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp [hμ]
  · have hμ : μ (p^(k+3-j)) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp [hμ]

noncomputable def lemma36AbsoluteConvolution {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ArithmeticFunction ℝ :=
  lemma36NormArithmeticFunction (lemma23UpsilonArithmeticFunction χ) *
    lemma36NormArithmeticFunction (lemma23NuArithmeticFunction χ)

lemma lemma36_absolute_convolution_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (lemma36AbsoluteConvolution χ).IsMultiplicative :=
  (lemma36_norm_arithmetic_multiplicative _ (lemma36_upsilon_multiplicative χ)).mul
    (lemma36_norm_arithmetic_multiplicative _ (lemma31_actual_nu_multiplicative χ))

lemma lemma36_absolute_convolution_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    0 ≤ lemma36AbsoluteConvolution χ n := by
  unfold lemma36AbsoluteConvolution
  rw [ArithmeticFunction.mul_apply]
  simp only [lemma36_norm_arithmetic_apply]
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma lemma36_absolute_convolution_prime_power_sum {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (k : ℕ) :
    lemma36AbsoluteConvolution χ (p^k) =
      ∑ j ∈ Finset.range (k+1), ‖lemma23UpsilonArithmeticFunction χ (p^j)‖ *
        ‖lemma23NuArithmeticFunction χ (p^(k-j))‖ := by
  rw [lemma36AbsoluteConvolution, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      lemma36NormArithmeticFunction (lemma23UpsilonArithmeticFunction χ) a *
        lemma36NormArithmeticFunction (lemma23NuArithmeticFunction χ) b),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.pow_div (show j ≤ k by have := Finset.mem_range.mp hj; omega) hp.pos]
  rfl

lemma lemma36_absolute_convolution_prime {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) :
    lemma36AbsoluteConvolution χ p = 2*‖lemma23NuArithmeticFunction χ p‖ := by
  have hu := (lemma36_upsilon_multiplicative χ).map_one
  have hn : lemma23NuArithmeticFunction χ p = 1+χ.evalNat p := by
    simpa [Finset.sum_range_succ] using lemma31_actual_nu_prime_power χ hp 1
  have hnorm : ‖lemma23UpsilonArithmeticFunction χ p‖ =
      ‖lemma23NuArithmeticFunction χ p‖ := by
    rw [lemma36_upsilon_prime χ hp, norm_neg, hn]
  have hh := lemma36_absolute_convolution_prime_power_sum χ hp 1
  simp only [pow_one] at hh
  rw [hh]
  simp [Finset.sum_range_succ, hu, lemma31_actual_nu_one, hnorm]
  ring

lemma lemma36_absolute_convolution_prime_power_tail {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (k : ℕ) :
    lemma36AbsoluteConvolution χ (p^(k+2)) =
      ‖lemma23NuArithmeticFunction χ (p^(k+2))‖ +
      ‖1+χ.evalNat p‖*‖lemma23NuArithmeticFunction χ (p^(k+1))‖ +
      ‖χ.evalNat p‖*‖lemma23NuArithmeticFunction χ (p^k)‖ := by
  rw [lemma36_absolute_convolution_prime_power_sum χ hp (k+2)]
  rw [show k+2+1 = (k+1)+1+1 by omega,
    Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : (∑ j ∈ Finset.range k,
      ‖lemma23UpsilonArithmeticFunction χ (p^(j+1+1+1))‖ *
        ‖lemma23NuArithmeticFunction χ (p^(k+2-(j+1+1+1)))‖) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [show j+1+1+1 = j+3 by omega, lemma36_upsilon_prime_power_ge_three χ hp]
    simp
  rw [hz]
  have hu := (lemma36_upsilon_multiplicative χ).map_one
  have hs1 : k+2-1 = k+1 := by omega
  simp only [Nat.reduceAdd, Nat.add_sub_cancel,
    Nat.sub_zero, pow_zero, pow_one, hu, norm_one, one_mul,
    lemma36_upsilon_prime χ hp, lemma36_upsilon_prime_square χ hp, norm_neg, zero_add, hs1]
  ring

lemma lemma36_nu_prime_power_two_step {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (hc : χ.evalNat p = -1) (k : ℕ) :
    lemma23NuArithmeticFunction χ (p^(k+2)) = lemma23NuArithmeticFunction χ (p^k) := by
  simp only [lemma31_actual_nu_prime_power χ hp, hc]
  rw [show k+2+1 = (k+1)+1+1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [pow_succ]
  ring

lemma lemma36_absolute_convolution_prime_power_le {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (hp : p.Prime) (e : ℕ) :
    lemma36AbsoluteConvolution χ (p^e) ≤
      ‖lemma23NuArithmeticFunction χ (p^e)‖ * (e+1 : ℝ) := by
  rcases e with _ | _ | k
  · simp [(lemma36_absolute_convolution_multiplicative χ).map_one,
      lemma31_actual_nu_one]
  · norm_num [lemma36_absolute_convolution_prime χ hp, mul_comm]
  · rw [lemma36_absolute_convolution_prime_power_tail χ hp k]
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p : ZMod D) with hc | hc | hc
    · have hc' : χ.evalNat p = 0 := hc
      have hn (j : ℕ) : lemma23NuArithmeticFunction χ (p^j) = 1 := by
        rw [lemma31_actual_nu_prime_power χ hp, hc']
        simp [zero_pow_eq]
      simp only [hn, hc', add_zero, norm_one, norm_zero, zero_mul, one_mul, add_zero]
      push_cast
      linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    · have hc' : χ.evalNat p = 1 := hc
      simp only [lemma31_actual_nu_prime_power_of_one χ hp hc', hc', Complex.norm_natCast]
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith [sq_nonneg (k : ℝ)]
    · have hc' : χ.evalNat p = -1 := hc
      simp only [hc', lemma36_nu_prime_power_two_step χ hp hc' k]
      norm_num only [add_neg_cancel, norm_zero, norm_neg, norm_one, zero_mul,
        one_mul, add_zero]
      have hn := norm_nonneg (lemma23NuArithmeticFunction χ (p^k))
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      nlinarith

lemma lemma36_absolute_convolution_le {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma36AbsoluteConvolution χ n ≤
      ‖lemma23NuArithmeticFunction χ n‖ * (lemma34Tau 2 n : ℝ) := by
  by_cases hn : n = 0
  · subst n; simp
  · have hC := lemma36_absolute_convolution_multiplicative χ
    have hN := lemma36_norm_arithmetic_multiplicative _ (lemma31_actual_nu_multiplicative χ)
    have hT : (ArithmeticFunction.zeta ^ 2 : ArithmeticFunction ℕ).IsMultiplicative :=
      lemma34_tau_multiplicative 2
    change lemma36AbsoluteConvolution χ n ≤
      lemma36NormArithmeticFunction (lemma23NuArithmeticFunction χ) n *
        (((ArithmeticFunction.zeta ^ 2 : ArithmeticFunction ℕ) n : ℕ) : ℝ)
    rw [hC.multiplicative_factorization _ hn, hN.multiplicative_factorization _ hn,
      hT.multiplicative_factorization _ hn]
    simp only [Finsupp.prod, Nat.cast_prod]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p hp
      exact lemma36_absolute_convolution_nonneg χ _
    · intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      change lemma36AbsoluteConvolution χ (p^n.factorization p) ≤
        ‖lemma23NuArithmeticFunction χ (p^n.factorization p)‖ *
          (lemma34Tau 2 (p^n.factorization p) : ℝ)
      rw [lemma32_tau_two_prime_power hp']
      simpa only [Nat.cast_add, Nat.cast_one] using
        lemma36_absolute_convolution_prime_power_le χ hp' (n.factorization p)

lemma lemma36_varsigma_norm_le {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23ActualVarsigma χ n‖ ≤
      ‖lemma23NuArithmeticFunction χ n‖ * (lemma34Tau 2 n : ℝ) := by
  calc
    _ ≤ ∑ q ∈ n.divisorsAntidiagonal with q.1 ≤ D^4 ∧ q.2 ≤ D^4,
        ‖lemma23NuArithmeticFunction χ q.1‖ *
          ‖lemma23UpsilonArithmeticFunction χ q.2‖ := by
      unfold lemma23ActualVarsigma
      simpa only [norm_mul] using norm_sum_le
        ((n.divisorsAntidiagonal).filter (fun q => q.1 ≤ D^4 ∧ q.2 ≤ D^4))
        (fun q => lemma23NuArithmeticFunction χ q.1 * lemma23UpsilonArithmeticFunction χ q.2)
    _ ≤ ∑ q ∈ n.divisorsAntidiagonal,
        ‖lemma23NuArithmeticFunction χ q.1‖ *
          ‖lemma23UpsilonArithmeticFunction χ q.2‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = lemma36AbsoluteConvolution χ n := by
      unfold lemma36AbsoluteConvolution
      rw [mul_comm (lemma36NormArithmeticFunction (lemma23UpsilonArithmeticFunction χ))
        (lemma36NormArithmeticFunction (lemma23NuArithmeticFunction χ)),
        ArithmeticFunction.mul_apply]
      rfl
    _ ≤ _ := lemma36_absolute_convolution_le χ n

lemma lemma36_varsigma_norm_square_le {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23ActualVarsigma χ n‖^2 ≤ lemma32ActualCoefficient χ n := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (lemma36_varsigma_norm_le χ n) 2
  simpa only [mul_pow, lemma32ActualCoefficient] using h

end ZhangLS.Spec
