import ZhangLS.Spec.Lemma151Basis
import ZhangLS.Spec.Lemma151LocalResidue
import ZhangLS.Spec.Lemma151WeightedError
import ZhangLS.Spec.Lemma151TailIntegral
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma151_rho_prime (β : ℂ) {p : ℕ} (hp : p.Prime) :
    lemma151Rho β p = 1-(p : ℂ)^β := by
  rw [lemma151_rho_divisor_sum, hp.divisors]
  simp [hp.ne_one.symm, ArithmeticFunction.moebius_apply_prime hp]
  ring

lemma lemma151_rhostar_prime {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) {p : ℕ} (hp : p.Prime) :
    lemma151RhoStar χ β p = 1+χ.evalNat p*(p : ℂ)^β := by
  rw [lemma151_rhostar_divisor_sum, hp.divisors]
  simp [hp.ne_one.symm]

/-- A negative-character prime keeps ρ*=ρ but its extra external χ reverses
its sign. Thus dropping the external χ without the b-basis conversion is invalid. -/
theorem lemma151_literal_external_character_sign {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) {p : ℕ} (hp : p.Prime)
    (hχ : χ.evalNat p = -1) :
    χ.evalNat p * lemma151RhoStar χ β p = -lemma151Rho β p := by
  rw [lemma151_rhostar_prime χ β hp, lemma151_rho_prime β hp, hχ]
  ring

/-- The two b conventions cannot be interchanged even on unramified arguments. -/
theorem lemma151_basis_not_interchangeable {D n : ℕ} (χ : RealPrimitiveCharacter D)
    (hχ : χ.evalNat n = -1) (hb : lemma151BChiPsi D n ≠ 0) :
    lemma151BPsi χ n ≠ lemma151BChiPsi D n := by
  unfold lemma151BPsi
  rw [hχ]
  intro he
  apply hb
  linear_combination (-1/2 : ℂ) * he

/-- At the literal B.3 cutoff P^12 the κ₁ kernel is already zero. This retains
the source exponent separately from the support-driven P^(1/2) correction. -/
theorem lemma151_literal_B3_support_zero {P : ℝ} (hP : 1 ≤ P)
    (β : ℂ) {n : ℕ} (hn : P^(12 : ℝ) < (n : ℝ)) :
    lemma151Kernel (P^(0.504 : ℝ)) β n = 0 := by
  have hpow : P^(0.504 : ℝ) ≤ P^(12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  unfold lemma151Kernel
  rw [if_neg]
  intro hh
  exact (not_lt.mpr (hpow.trans hn.le)) hh.2

/-- H14 is zero on its strict cutoff's boundary, which belongs to H15. -/
theorem lemma151_H14_endpoint (D n : ℕ)
    (hn : (n : ℝ) = (lemma23PaperP D)^(1/2 : ℝ)) :
    lemma151First D n =
      lemma151Iota2 * lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) n := by
  unfold lemma151First
  rw [if_neg (by rw [hn]; exact lt_irrefl _), zero_add]

/-- The smooth n₁ domain is not made vacuous: 1 is always supported. -/
lemma lemma151_supported_one (Q : ℕ) : Lemma151Supported Q 1 := by
  refine ⟨by decide, ?_⟩
  intro q hq hq1
  have he := Nat.eq_one_of_dvd_one hq1
  exact (hq.ne_one he).elim

end ZhangLS.Spec


#print axioms ZhangLS.Spec.lemma151Twist
#print axioms ZhangLS.Spec.lemma151_twist_mul
#print axioms ZhangLS.Spec.lemma151_mu_mul_actual_nu
#print axioms ZhangLS.Spec.lemma151Rho
#print axioms ZhangLS.Spec.lemma151RhoStar
#print axioms ZhangLS.Spec.lemma151_rho_divisor_sum
#print axioms ZhangLS.Spec.lemma151_rhostar_divisor_sum
#print axioms ZhangLS.Spec.lemma151_rhostar_actual_nu_convolution
#print axioms ZhangLS.Spec.lemma151_moebius_norm_le_one
#print axioms ZhangLS.Spec.lemma151_power_norm
#print axioms ZhangLS.Spec.lemma151_rho_norm_le_tau
#print axioms ZhangLS.Spec.lemma151_rhostar_sub_rho_exact
#print axioms ZhangLS.Spec.lemma151_rhostar_sub_rho_bound
#print axioms ZhangLS.Spec.lemma151P1
#print axioms ZhangLS.Spec.lemma151P2
#print axioms ZhangLS.Spec.lemma151P3
#print axioms ZhangLS.Spec.lemma151Beta6
#print axioms ZhangLS.Spec.lemma151Beta7
#print axioms ZhangLS.Spec.lemma151Iota2
#print axioms ZhangLS.Spec.lemma151Iota3
#print axioms ZhangLS.Spec.lemma151Iota4
#print axioms ZhangLS.Spec.lemma151Kernel
#print axioms ZhangLS.Spec.lemma151First
#print axioms ZhangLS.Spec.lemma151Second
#print axioms ZhangLS.Spec.lemma151BChiPsi
#print axioms ZhangLS.Spec.lemma151BPsi
#print axioms ZhangLS.Spec.lemma151Q
#print axioms ZhangLS.Spec.Lemma151Supported
#print axioms ZhangLS.Spec.lemma151ArithmeticSum
#print axioms ZhangLS.Spec.lemma151FullKernelConstant
#print axioms ZhangLS.Spec.lemma151PrintedTail
#print axioms ZhangLS.Spec.lemma151ResidueTail
#print axioms ZhangLS.Spec.lemma151MainConstant
#print axioms ZhangLS.Spec.Lemma151OriginalTarget
#print axioms ZhangLS.Spec.lemma151_actual_psi_coefficient
#print axioms ZhangLS.Spec.lemma151_character_square
#print axioms ZhangLS.Spec.lemma151_psi_basis_character_cancellation
#print axioms ZhangLS.Spec.lemma151_prime_dvd_Q
#print axioms ZhangLS.Spec.lemma151_rough_coprime_modulus
#print axioms ZhangLS.Spec.lemma151_psi_basis_rough_cancellation
#print axioms ZhangLS.Spec.lemma151ArithmeticReplacementError
#print axioms ZhangLS.Spec.lemma151_weighted_rhostar_replacement
#print axioms ZhangLS.Spec.lemma151_rough_weighted_replacement
#print axioms ZhangLS.Spec.lemma151TailNumerator
#print axioms ZhangLS.Spec.lemma151TailIntegrand
#print axioms ZhangLS.Spec.lemma151TailRegularized
#print axioms ZhangLS.Spec.lemma151_tail_numerator_at_gamma
#print axioms ZhangLS.Spec.lemma151_tail_numerator_differentiable
#print axioms ZhangLS.Spec.lemma151_tail_gamma_quotient_differentiable
#print axioms ZhangLS.Spec.lemma151_tail_gamma_quotient_eq
#print axioms ZhangLS.Spec.lemma151_tail_regularized_eq
#print axioms ZhangLS.Spec.lemma151ExactTailResidue
#print axioms ZhangLS.Spec.lemma151_tail_regularized_at_zero
#print axioms ZhangLS.Spec.lemma151_tail_regularized_continuousAt_zero
#print axioms ZhangLS.Spec.lemma151_actual_tail_residue_limit
#print axioms ZhangLS.Spec.lemma151_reciprocal_zeta_factor
#print axioms ZhangLS.Spec.lemma151_actual_imaginary_tail_residue_limit
#print axioms ZhangLS.Spec.lemma151_exact_tail_residue_factorization
#print axioms ZhangLS.Spec.lemma151_exact_tail_residue_error
#print axioms ZhangLS.Spec.lemma151_short_exponential_integral
#print axioms ZhangLS.Spec.lemma151BStar
#print axioms ZhangLS.Spec.lemma151_residue_tail_eq_neg_pi_I_bstar
#print axioms ZhangLS.Spec.lemma151_rho_prime
#print axioms ZhangLS.Spec.lemma151_rhostar_prime
#print axioms ZhangLS.Spec.lemma151_literal_external_character_sign
#print axioms ZhangLS.Spec.lemma151_basis_not_interchangeable
#print axioms ZhangLS.Spec.lemma151_literal_B3_support_zero
#print axioms ZhangLS.Spec.lemma151_H14_endpoint
#print axioms ZhangLS.Spec.lemma151_supported_one
