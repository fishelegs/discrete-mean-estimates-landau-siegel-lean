import ZhangLS.Spec.Lemma162ActualCoefficientNorm
import ZhangLS.Spec.Lemma162PrimeSupportedSeries

/-! Actual absolute convergence and exceptional-prime Dirichlet/Euler bridge.
This does not yet claim holomorphy of the corrected extracted product. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_arithmetic_term_mul (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (s : ℂ) {m n : ℕ} (h : m.Coprime n) :
    LSeries.term f s (m*n) = LSeries.term f s m*LSeries.term f s n := by
  by_cases hm : m=0
  · subst m; simp
  by_cases hn : n=0
  · subst n; simp
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn),LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn,hf.map_mul_of_coprime h,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  exact mul_div_mul_comm _ _ _ _

lemma lemma162_actual_odd_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    LSeriesSummable (lemma162OddCoefficientArithmetic χ β γ) s := by
  obtain ⟨C,hC,hlocal⟩ := lemma162_actual_odd_local_norm_series χ β hβ γ hγ hB
  have hf := lemma162_odd_coefficient_multiplicative χ β hβ γ hγ hB
  apply summable_norm_iff.mp
  apply EulerProduct.summable_norm_of_prime_power_tsum_le
    (LSeries.term (lemma162OddCoefficientArithmetic χ β γ) s) (by simp)
    (by simp [LSeries.term,hf.map_one])
    (fun h => lemma162_arithmetic_term_mul _ hf s h)
    (fun hp => by
      simpa only [lemma162_arithmetic_prime_power_term _ hp.pos] using
        (hlocal _ hp (lemma32PrimeMonomial _ s) (lemma152_monomial_norm_half hp s hs.le)).1)
    (fun p => C*(p:ℝ)^(-s.re)) (fun p => mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (((Real.summable_nat_rpow.mpr (by linarith : -s.re < -1)).subtype Nat.Prime).mul_left C)
  intro p hp
  simpa only [lemma162_arithmetic_prime_power_term _ hp.pos,lemma83_prime_monomial_norm_rpow hp.pos] using
    (hlocal p hp (lemma32PrimeMonomial p s) (lemma152_monomial_norm_half hp s hs.le)).2

lemma lemma162_actual_odd_dirichlet_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    HasProd (fun q : Nat.Primes => ∑' r : ℕ,
      lemma162OddCoefficientArithmetic χ β γ (q.val^r)*lemma32PrimeMonomial q.val s^r)
      (LSeries (lemma162OddCoefficientArithmetic χ β γ) s) := by
  have hf := lemma162_odd_coefficient_multiplicative χ β hβ γ hγ hB
  have hh := EulerProduct.eulerProduct_hasProd
    (f := LSeries.term (lemma162OddCoefficientArithmetic χ β γ) s)
    (by simp [LSeries.term,hf.map_one])
    (fun {m n} h => lemma162_arithmetic_term_mul _ hf s h)
    (lemma162_actual_odd_lseries_summable χ β hβ γ hγ hB s hs).norm (LSeries.term_zero _ s)
  change HasProd _ (∑' n : ℕ, LSeries.term (lemma162OddCoefficientArithmetic χ β γ) s n)
  apply hh.congr_fun
  intro q
  apply tsum_congr
  intro r
  exact (lemma162_arithmetic_prime_power_term _ q.property.pos s r).symm

lemma lemma162_actual_two_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0) (s : ℂ) (hs : 1<s.re) :
    LSeriesSummable (lemma162TwoCoefficientArithmetic χ β γ) s := by
  have hsum := summable_norm_iff.mp
    (lemma162_actual_two_local_norm_series χ β hβ γ hγ (lemma32PrimeMonomial 2 s)
      (lemma152_monomial_norm_half Nat.prime_two s hs.le)).1
  rw [lemma162TwoCoefficientArithmetic,lemma162_prime_power_part_pmul]
  apply lemma162_prime_supported_lseries_summable Nat.prime_two
  simpa only [lemma162TwoCoefficientArithmetic,ArithmeticFunction.pmul_apply,
    lemma162_prime_power_part_apply] using hsum

lemma lemma162_actual_two_lseries_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0) (s : ℂ) (hs : 1<s.re) :
    LSeries (lemma162TwoCoefficientArithmetic χ β γ) s =
      ∑' r : ℕ, lemma162TwoCoefficientArithmetic χ β γ (2^r)*lemma32PrimeMonomial 2 s^r := by
  have hsum := summable_norm_iff.mp
    (lemma162_actual_two_local_norm_series χ β hβ γ hγ (lemma32PrimeMonomial 2 s)
      (lemma152_monomial_norm_half Nat.prime_two s hs.le)).1
  rw [lemma162TwoCoefficientArithmetic,lemma162_prime_power_part_pmul]
  apply lemma162_prime_supported_lseries_eq Nat.prime_two
  convert hsum.hasSum using 1
  · funext r
    simp only [lemma162TwoCoefficientArithmetic,ArithmeticFunction.pmul_apply,lemma162_prime_power_part_apply]
  · simp only [lemma162TwoCoefficientArithmetic,ArithmeticFunction.pmul_apply,lemma162_prime_power_part_apply]

/-- Absolute convergence of the literal original Lemma16.2 coefficient. -/
lemma lemma162_actual_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    LSeriesSummable (lemma162Coefficient χ β γ (lemma162GeneralMEulerProduct χ β)) s := by
  have hB := (lemma162_odd_baseline_nonzero χ β hβ (1-γ)
    (by simp [hγ]; norm_num) hstar).1
  change LSeriesSummable (lemma162ActualCoefficientArithmetic χ β γ) s
  rw [lemma162_actual_coefficient_reassembly χ β hβ γ hγ hstar]
  exact ArithmeticFunction.LSeriesSummable_mul
    (lemma162_actual_two_lseries_summable χ β hβ γ hγ s hs)
    (lemma162_actual_odd_lseries_summable χ β hβ γ hγ hB s hs)

lemma lemma162_actual_dirichlet_two_odd_product {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s =
      LSeries (lemma162TwoCoefficientArithmetic χ β γ) s *
        LSeries (lemma162OddCoefficientArithmetic χ β γ) s := by
  have hB := (lemma162_odd_baseline_nonzero χ β hβ (1-γ)
    (by simp [hγ]; norm_num) hstar).1
  change LSeries (lemma162ActualCoefficientArithmetic χ β γ) s = _
  rw [lemma162_actual_coefficient_reassembly χ β hβ γ hγ hstar]
  exact ArithmeticFunction.LSeries_mul'
    (lemma162_actual_two_lseries_summable χ β hβ γ hγ s hs)
    (lemma162_actual_odd_lseries_summable χ β hβ γ hγ hB s hs)

lemma lemma162_odd_coefficient_two_succ {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (r : ℕ) : lemma162OddCoefficientArithmetic χ β γ (2^(r+1)) = 0 := by
  have hn : ¬(2^(r+1):ℕ).Coprime 2 := by
    intro h
    have hdiv : (2:ℕ) ∣ 2^(r+1) := dvd_pow_self 2 (by omega)
    exact Nat.prime_two.ne_one (Nat.eq_one_of_dvd_coprimes h hdiv (dvd_refl 2))
  simp only [lemma162OddCoefficientArithmetic,lemma162OddRestriction,ArithmeticFunction.coe_mk,if_neg hn]

lemma lemma162_odd_two_local_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0) (z : ℂ) :
    (∑' r : ℕ, lemma162OddCoefficientArithmetic χ β γ (2^r)*z^r) = 1 := by
  rw [tsum_eq_single 0]
  · simpa only [pow_zero,mul_one] using
      (lemma162_odd_coefficient_multiplicative χ β hβ γ hγ hB).map_one
  · intro r hr
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    simp only [lemma162_odd_coefficient_two_succ,zero_mul]

noncomputable def lemma162ActualLocalSeries {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  if q = lemma162PrimeTwo then
    ∑' r : ℕ, lemma162TwoCoefficientArithmetic χ β γ (2^r)*lemma32PrimeMonomial 2 s^r
  else ∑' r : ℕ, lemma162OddCoefficientArithmetic χ β γ (q.val^r)*lemma32PrimeMonomial q.val s^r

/-- A genuine Euler identity for the original coefficients. Its q=2 local
constant is allowed to differ from1, exactly as the source normalization demands. -/
lemma lemma162_actual_dirichlet_series_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    HasProd (fun q : Nat.Primes => lemma162ActualLocalSeries χ β γ q s)
      (lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s) := by
  have hB := (lemma162_odd_baseline_nonzero χ β hβ (1-γ)
    (by simp [hγ]; norm_num) hstar).1
  have hodd := lemma162_actual_odd_dirichlet_hasProd χ β hβ γ hγ hB s hs
  have htwo := lemma153_finite_ite_hasProd ({lemma162PrimeTwo} : Finset Nat.Primes)
    (fun _q => LSeries (lemma162TwoCoefficientArithmetic χ β γ) s)
  simp only [prod_singleton] at htwo
  rw [lemma162_actual_dirichlet_two_odd_product χ β hβ γ hγ hstar s hs]
  apply (htwo.mul hodd).congr_fun
  intro q
  by_cases hq : q = lemma162PrimeTwo
  · subst q
    simp only [lemma162ActualLocalSeries,mem_singleton_self,if_true]
    rw [lemma162_actual_two_lseries_eq χ β hβ γ hγ s hs]
    simp only [lemma162PrimeTwo,lemma162_odd_two_local_series χ β hβ γ hγ hB,mul_one]
  · simp [lemma162ActualLocalSeries,hq]

end ZhangLS.Spec
