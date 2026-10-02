import ZhangLS.Spec.Lemma57SmoothedSum
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Positivity of Zhang's divisor-character coefficient

For a quadratic Dirichlet character `χ`, mathlib defines the arithmetic function

  `χ.zetaMul = ζ * χ`

and proves that all of its values are nonnegative real complex numbers.  The coefficient
used in this formalization,

  `divisorCharacterSum χ n = ∑ d ∣ n, χ(d)`,

is exactly the same Dirichlet-convolution coefficient.  This file records the bridge and
thereby closes the last arithmetic sign hypothesis in the finite smoothed-sum argument.
-/

namespace ZhangLS.Spec

open scoped BigOperators ComplexOrder

/-- Our explicit divisor sum is exactly mathlib's `DirichletCharacter.zetaMul` coefficient. -/
theorem divisorCharacterSum_eq_zetaMul
    {D n : ℕ} (χ : RealPrimitiveCharacter D) :
    divisorCharacterSum χ n = χ.chi.zetaMul n := by
  unfold divisorCharacterSum DirichletCharacter.zetaMul
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  simpa [RealPrimitiveCharacter.evalNat] using
    χ.chi.apply_eq_toArithmeticFunction_apply hd0

/-- Zhang's coefficient `νχ(n)` is nonnegative for every `n`.

This is not an additional assumption: it follows from the quadratic identity `χ² = 1`
and mathlib's prime-power/multiplicativity proof of `DirichletCharacter.zetaMul_nonneg`. -/
theorem divisorCharacterSumReal_nonneg
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    0 ≤ divisorCharacterSumReal χ n := by
  have hcomplex : (0 : ℂ) ≤ χ.chi.zetaMul n :=
    DirichletCharacter.zetaMul_nonneg χ.quadratic n
  have hre : 0 ≤ (χ.chi.zetaMul n).re := (Complex.nonneg_iff.mp hcomplex).1
  unfold divisorCharacterSumReal
  rw [divisorCharacterSum_eq_zetaMul χ]
  simpa using hre

/-- The sign interface introduced in Step 16 is now discharged unconditionally. -/
theorem divisorCharacterSumNonnegative_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) :
    DivisorCharacterSumNonnegative χ := by
  intro n
  exact divisorCharacterSumReal_nonneg χ n

/-- Unconditional form of the Step-16 finite Gaussian arithmetic lower bound. -/
theorem lemma57_initial_gaussian_arithmetic_scale_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (1 : ℝ) / 8 * lemma57Scale D ≤
      lemma57InitialSmoothedSum χ (zhangGaussianWeight D) := by
  exact lemma57_initial_gaussian_arithmetic_scale χ
    (divisorCharacterSumNonnegative_proved χ) hD

/-- Unconditional arithmetic input for the Step-08 contour-transfer interface. -/
noncomputable def lemma57InitialArithmeticLowerBound_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57ArithmeticLowerBound D :=
  lemma57InitialArithmeticLowerBound χ (divisorCharacterSumNonnegative_proved χ) hD

end ZhangLS.Spec
