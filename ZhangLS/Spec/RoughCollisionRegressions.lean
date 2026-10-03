import ZhangLS.Spec.RoughCollisionSmoothSplit
import ZhangLS.Spec.BSourceRegressions

/-! Source and endpoint regressions. Same-line attributes are deliberately used
on some declarations; the validation inventory includes them. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical ComplexConjugate

@[simp] theorem roughCollision_rho_prime_exact (β : ℂ) {p : ℕ} (hp : p.Prime) :
    lemma151Rho β p=1-(p : ℂ)^β := by
  rw [lemma151_rho_divisor_sum,hp.divisors]
  simp [hp.ne_one.symm,ArithmeticFunction.moebius_apply_prime hp]
  ring

@[simp] theorem roughCollision_rho_prime_square_exact (β : ℂ) {p : ℕ} (hp : p.Prime) :
    lemma151Rho β (p^2)=1-(p : ℂ)^β := by
  rw [lemma151_rho_divisor_sum,Nat.sum_divisors_prime_pow hp]
  simp [Finset.sum_range_succ,ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime_pow hp (by decide : (2 : ℕ)≠0)]
  ring

/-- The collision defect is generally nonzero: coprimality cannot be dropped
from rho multiplicativity. This retains the actual complex-power phase. -/
theorem roughCollision_prime_collision_identity (β : ℂ) {p : ℕ} (hp : p.Prime) :
    lemma151Rho β (p*p)-lemma151Rho β p*lemma151Rho β p =
      (p : ℂ)^β*(1-(p : ℂ)^β) := by
  rw [←pow_two,roughCollision_rho_prime_square_exact β hp,roughCollision_rho_prime_exact β hp]
  ring

/-- Source H14 is strictly truncated. The >= tail includes equality. -/
theorem roughCollision_H14_boundary (D n : ℕ)
    (hn : (n : ℝ)=(lemma23PaperP D)^(1/2 : ℝ)) : bH14Coefficient D n=0 := by
  simp [bH14Coefficient,hn]

/-- The literal printed P^12 cutoff is retained as an independently vanishing
region, rather than being silently renamed P^(1/2). -/
theorem roughCollision_literal_B3_zero {P : ℝ} (hP : 1≤P)
    (β : ℂ) {n : ℕ} (hn : P^(12 : ℝ)<(n : ℝ)) :
    lemma151Kernel (P^(0.504 : ℝ)) β n=0 := by
  have hh : P^(0.504 : ℝ)≤P^(12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  unfold lemma151Kernel
  rw [if_neg]
  exact fun h => (not_lt_of_ge (hh.trans hn.le)) h.2

/-- The U coefficient in the collision bound retains P2's T^-10 exactly. -/
theorem roughCollision_U_expanded (D n : ℕ) :
    lemma151First D n =
      (if (n : ℝ)<(lemma23PaperP D)^(1/2 : ℝ)
       then lemma151Kernel ((lemma23PaperP D)^(0.504 : ℝ))
         (3*I*(lemma44PaperAlpha D : ℂ)/2) n else 0) +
      (0.94977-1.38995*I)*lemma151Kernel
        ((lemma23PaperP D)^(0.5 : ℝ)*lemma56PaperT D^(-10 : ℤ))
        (5*I*(lemma44PaperAlpha D : ℂ)/2) n := rfl

theorem roughCollision_V_expanded (D n : ℕ) :
    lemma151Second D n =
      conj (-1.00635-0.22789*I)*lemma151Kernel ((lemma23PaperP D)^(0.498 : ℝ))
        (3*I*(lemma44PaperAlpha D : ℂ)/2) n +
      conj (-0.68738+1.60688*I)*lemma151Kernel
        ((lemma23PaperP D)^(0.5 : ℝ)*lemma56PaperT D^(-10 : ℤ))
        (5*I*(lemma44PaperAlpha D : ℂ)/2) n := rfl

theorem roughCollision_rough_domain_expanded (D X n : ℕ) :
    n∈roughCollisionDomain D X ↔
      1≤n ∧ n≤X ∧ n.Coprime (∏q ∈ (range (D^4)).filter Nat.Prime, q) := by
  simp [roughCollisionDomain,lemma151Q,and_assoc]

/-- Small primes are excluded at the original strict boundary. -/
theorem roughCollision_small_prime_excluded {D X p : ℕ}
    (hp : p.Prime) (hsmall : p<D^4) : p∉roughCollisionDomain D X := by
  intro h
  have hrough := (mem_filter.mp h).2
  have hlower := roughCollision_common_prime_lower hrough hp (dvd_refl p)
  omega

/-- The factor C is exactly the original U,V norm constant. -/
theorem roughCollision_constant_expanded : bCoefficientConstant =
    (1+‖(0.94977-1.38995*I : ℂ)‖)*
      (‖(-1.00635-0.22789*I : ℂ)‖+‖(-0.68738+1.60688*I : ℂ)‖) := rfl

/-- A smooth n1 need not be zero or empty; 1 belongs to every original domain. -/
theorem roughCollision_supported_one (D : ℕ) : Lemma151Supported (lemma151Q D) 1 := by
  refine ⟨by decide,?_⟩
  intro p hp hp1
  exact (hp.ne_one (Nat.eq_one_of_dvd_one hp1)).elim

/-- There is no uniform replacement of rho-star by rho hidden in this package:
the true nu convolution remains the upstream identity. -/
theorem roughCollision_rhostar_is_actual_nu {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) :
    lemma151RhoStar χ (lemma83PaperBeta D c j) =
      lemma151Rho (lemma83PaperBeta D c j)*
        lemma151Twist (lemma83PaperBeta D c j) (lemma23NuArithmeticFunction χ) :=
  lemma151_rhostar_actual_nu_convolution χ _

end ZhangLS.Spec
