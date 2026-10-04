import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.Lemma34TauProduct

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ZhangLS.Spec

open Finset
open scoped Classical ArithmeticFunction.zeta

/-- Generalized divisor functions are submultiplicative in their argument. -/
theorem ramified_tau_mul_le (k a b : ℕ) (_hk : 0 < k) :
    lemma34Tau k (a*b) ≤ lemma34Tau k a * lemma34Tau k b :=
  proposition71_tau_submultiplicative k a b

theorem ramified_tau_mul_le_real (k a b : ℕ) (hk : 0 < k) :
    (lemma34Tau k (a*b) : ℝ) ≤ (lemma34Tau k a : ℝ)*(lemma34Tau k b : ℝ) := by
  exact_mod_cast ramified_tau_mul_le k a b hk

/-- Dirichlet convolution adds the orders of the actual divisor functions. -/
theorem ramified_tau_convolution (k l D : ℕ) :
    (∑ g ∈ D.divisors, lemma34Tau k g * lemma34Tau l (D/g)) =
      lemma34Tau (k+l) D := by
  unfold lemma34Tau
  rw [pow_add, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => (ArithmeticFunction.zeta^k) x *
      (ArithmeticFunction.zeta^l) y)]

theorem ramified_tau_convolution_real (k l D : ℕ) :
    (∑ g ∈ D.divisors, (lemma34Tau k g : ℝ)*(lemma34Tau l (D/g) : ℝ)) =
      (lemma34Tau (k+l) D : ℝ) := by
  exact_mod_cast ramified_tau_convolution k l D

theorem ramified_tau_four_convolution (D : ℕ) :
    (∑ g ∈ D.divisors, (lemma34Tau 4 g : ℝ)*(lemma34Tau 4 (D/g) : ℝ)) =
      (lemma34Tau 8 D : ℝ) := by
  simpa using ramified_tau_convolution_real 4 4 D

end ZhangLS.Spec
