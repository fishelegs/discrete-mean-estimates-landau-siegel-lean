import ZhangLS.Spec.Lemma83XiLocalAbsolute

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- The genuine Dirichlet convolution μ*ξ. -/
noncomputable def lemma83XiMoebius (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) :
    ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ)*lemma83XiArithmetic β j d r

lemma lemma83_xi_moebius_multiplicative (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) (d r : ℕ) :
    (lemma83XiMoebius β j d r).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (lemma83_xi_multiplicative β hβ j d r)

/-- Exact inversion for the actual divisor-sum coefficient. -/
theorem lemma83_xi_moebius_inversion (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*lemma83XiMoebius β j d r =
      lemma83XiArithmetic β j d r := by
  rw [lemma83XiMoebius,←mul_assoc,ArithmeticFunction.coe_zeta_mul_coe_moebius,one_mul]

theorem lemma83_xi_eq_sum_moebius (β : Fin 3 → ℂ) (j : Fin 3) (n d r : ℕ) :
    lemma83Xi β j n d r = ∑ k ∈ n.divisors, lemma83XiMoebius β j d r k := by
  have hh := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (lemma83_xi_moebius_inversion β j d r)
  dsimp only at hh
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hh
  exact hh.symm

@[simp] lemma lemma83_xi_moebius_one (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) :
    lemma83XiMoebius β j d r 1 = 1 := by
  simp [lemma83XiMoebius,ArithmeticFunction.mul_apply,lemma83XiArithmetic]

lemma lemma83_xi_moebius_prime_power (β : Fin 3 → ℂ) (j : Fin 3) {p : ℕ}
    (hp : p.Prime) (e d r : ℕ) :
    lemma83XiMoebius β j d r (p^(e+1)) =
      lemma83Xi β j (p^(e+1)) d r-lemma83Xi β j (p^e) d r :=
  lemma83_moebius_convolution_prime_power_succ (lemma83XiArithmetic β j d r) hp e

end ZhangLS.Spec
