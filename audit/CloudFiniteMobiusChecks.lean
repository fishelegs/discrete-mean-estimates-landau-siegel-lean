import ZhangLS.Spec.FiniteMobius
import Mathlib.Data.Complex.Basic

open ArithmeticFunction ZhangLS.Spec.FiniteMobius

/- Exact theorem applications, deliberately without native_decide or numerical approximation. -/
example {U J n : ℕ} (hJ : 0 < J) (hn : n ≤ U ^ J) :
    (moebius n : ℂ) =
      ∑ j ∈ Finset.range J,
        (((-1 : ℤ) ^ j * (J.choose (j + 1) : ℤ) : ℤ) : ℂ) *
          (truncated (R := ℂ) U ^ (j + 1) * (zeta : ArithmeticFunction ℂ) ^ j) n :=
  finite_moebius_identity hJ hn

example (U : ℕ) :
    (moebius (U ^ 4) : ℂ) =
      4 * truncated (R := ℂ) U (U ^ 4) -
      6 * (truncated (R := ℂ) U ^ 2 * (zeta : ArithmeticFunction ℂ)) (U ^ 4) +
      4 * (truncated (R := ℂ) U ^ 3 * (zeta : ArithmeticFunction ℂ) ^ 2) (U ^ 4) -
      (truncated (R := ℂ) U ^ 4 * (zeta : ArithmeticFunction ℂ) ^ 3) (U ^ 4) :=
  finite_moebius_identity_four le_rfl

example (U : ℕ) : truncated (R := ℤ) U U = moebius U := by simp
example (U : ℕ) : truncated (R := ℤ) U (U + 1) = 0 := by simp
example {U : ℕ} (hU : 1 ≤ U) : defect (R := ℂ) U 1 = 0 := defect_eq_zero hU
example {U J : ℕ} (hJ : 0 < J) : (defect (R := ℂ) U ^ J) (U ^ J) = 0 :=
  defect_pow_eq_zero hJ le_rfl

#print axioms ZhangLS.Spec.FiniteMobius.binomial_inverse_identity
#print axioms ZhangLS.Spec.FiniteMobius.finite_moebius_identity
#print axioms ZhangLS.Spec.FiniteMobius.finite_moebius_identity_four
#print axioms ZhangLS.Spec.FiniteMobius.finite_moebius_identity_endpoint
#print axioms ZhangLS.Spec.FiniteMobius.finite_moebius_identity_one
