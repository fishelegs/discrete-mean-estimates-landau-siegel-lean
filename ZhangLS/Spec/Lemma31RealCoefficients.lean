import ZhangLS.Spec.Lemma31SquareMajorant
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ComplexOrder
set_option maxHeartbeats 2000000

noncomputable def lemma31NuReal {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) : ℝ :=
  (lemma23NuArithmeticFunction χ n).re

lemma lemma31_nu_real_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    0 ≤ lemma31NuReal χ n := (Complex.nonneg_iff.mp (lemma31_actual_nu_nonneg χ n)).1

lemma lemma31_nu_real_eq_norm {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma31NuReal χ n = ‖lemma23NuArithmeticFunction χ n‖ :=
  Complex.re_eq_norm.mpr (lemma31_actual_nu_nonneg χ n)

lemma lemma31_nu_real_eq_divisor_sum {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma31NuReal χ n = divisorCharacterSumReal χ n := by
  unfold lemma31NuReal divisorCharacterSumReal
  rw [lemma31_actual_nu_eq_zetaMul,divisorCharacterSum_eq_zetaMul χ]

lemma lemma31_nu_im_zero {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    (lemma23NuArithmeticFunction χ n).im = 0 :=
  (Complex.nonneg_iff.mp (lemma31_actual_nu_nonneg χ n)).2.symm

lemma lemma31_nu_convolution_real {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ((lemma23NuArithmeticFunction χ * lemma23NuArithmeticFunction χ) n).re =
      ∑ q ∈ n.divisorsAntidiagonal, lemma31NuReal χ q.1 * lemma31NuReal χ q.2 := by
  rw [ArithmeticFunction.mul_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp [Complex.mul_re,lemma31_nu_im_zero,lemma31NuReal]

lemma lemma31_nu_norm_square_le_divisor_convolution {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23NuArithmeticFunction χ n‖^2 ≤
      ∑ q ∈ n.divisorsAntidiagonal, lemma31NuReal χ q.1 * lemma31NuReal χ q.2 := by
  rw [← lemma31_nu_convolution_real]
  exact lemma31_actual_nu_norm_square_le_convolution χ n

end ZhangLS.Spec
