import ZhangLS.Spec.Lemma162RawLocalSeries
import ZhangLS.Spec.Lemma162ActualDirichletSeries

/-! Match every original prime-power coefficient to the exact raw local
kernel. q=2 uses N₂; odd primes use only their nonzero odd baseline factor. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def lemma162Local00 {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) : ℂ := lemma161PrimeFactor χ β q (1-γ)
noncomputable def lemma162Local01 {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) : ℂ := lemma162GeneralMPrimeFactor χ β 1 q.val q (1-γ)
noncomputable def lemma162Local10 {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) : ℂ := lemma162GeneralMPrimeFactor χ β q.val 1 q (1-γ)
noncomputable def lemma162Local11 {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) : ℂ := lemma162GeneralMPrimeFactor χ β q.val q.val q (1-γ)

noncomputable def lemma162LocalNormalizer {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) : ℂ :=
  if q=lemma162PrimeTwo then lemma162TwoNormalizer χ β (1-γ) else lemma162Local00 χ β γ q

noncomputable def lemma162RawPrimeCoefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (q : Nat.Primes) (n : ℕ) : ℂ :=
  lemma162RawCoefficient (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
    (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q) (lemma161LambdaFactor χ β q.val 1)
      ((q.val:ℂ)^γ) (χ.evalNat q.val) n *
    lemma83LocalH3 1 (χ.evalNat q.val) (χ.evalNat q.val) n

lemma lemma162_local_kernel_prime_power {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ N : ℂ) (q : Nat.Primes) (i j : ℕ) :
    lemma161Lambda χ β (q.val^i)*((q.val^i:ℕ):ℂ)^γ*χ.evalNat (q.val^j)*
      (lemma162GeneralMPrimeFactor χ β (q.val^i) (q.val^j) q (1-γ)/N) =
    lemma162RawKernel (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
      (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q)
      (lemma161LambdaFactor χ β q.val 1) ((q.val:ℂ)^γ) (χ.evalNat q.val) i j / N := by
  have hchi : χ.evalNat (q.val^j) = χ.evalNat q.val^j := by
    simp [RealPrimitiveCharacter.evalNat,Nat.cast_pow,map_pow]
  rw [lemma162_lambda_prime_power χ β q.property,lemma162_nat_power_cpow,hchi,
    lemma162_general_m_prime_power_flags]
  unfold lemma162RawKernel lemma162Local00 lemma162Local01 lemma162Local10 lemma162Local11
  ring

lemma lemma162_odd_kernel_raw_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0)
    (q : Nat.Primes) (hq : 2<q.val) (i j : ℕ) :
    lemma162OddVarpiKernel χ β γ (q.val^i) (q.val^j) =
    lemma162RawKernel (lemma162Local00 χ β γ q) (lemma162Local01 χ β γ q)
      (lemma162Local10 χ β γ q) (lemma162Local11 χ β γ q)
      (lemma161LambdaFactor χ β q.val 1) ((q.val:ℂ)^γ) (χ.evalNat q.val) i j /
        lemma162Local00 χ β γ q := by
  unfold lemma162OddVarpiKernel
  rw [lemma162_odd_m_prime_power_ratio χ β hβ q hq i j (1-γ) (by simp [hγ]; norm_num) hB]
  exact lemma162_local_kernel_prime_power χ β γ _ q i j

lemma lemma162_two_kernel_raw_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (i j : ℕ) :
    lemma162TwoVarpiKernel χ β γ (2^i) (2^j) =
    lemma162RawKernel (lemma162Local00 χ β γ lemma162PrimeTwo) (lemma162Local01 χ β γ lemma162PrimeTwo)
      (lemma162Local10 χ β γ lemma162PrimeTwo) (lemma162Local11 χ β γ lemma162PrimeTwo)
      (lemma161LambdaFactor χ β 2 1) ((2:ℂ)^γ) (χ.evalNat 2) i j /
        lemma162TwoNormalizer χ β (1-γ) :=
  lemma162_local_kernel_prime_power χ β γ _ lemma162PrimeTwo i j

lemma lemma162_odd_prime_coprime_two (q : Nat.Primes) (hq : 2<q.val) : q.val.Coprime 2 := by
  apply q.property.coprime_iff_not_dvd.mpr
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact q.property.ne_one h
  · omega

lemma lemma162_odd_prime_power_raw_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0)
    (q : Nat.Primes) (hq : 2<q.val) (n : ℕ) :
    lemma162OddCoefficientArithmetic χ β γ (q.val^n) =
      lemma162RawPrimeCoefficient χ β γ q n / lemma162Local00 χ β γ q := by
  have hcop : (q.val^n).Coprime 2 := (lemma162_odd_prime_coprime_two q hq).pow_left n
  change (if (q.val^n).Coprime 2 then
    lemma162OddVarpiArithmetic χ β γ (q.val^n)*lemma162NuChi χ (q.val^n) else 0) = _
  rw [if_pos hcop,lemma162_nu_chi_prime_power_h3 χ q.property]
  unfold lemma162OddVarpiArithmetic
  rw [lemma162_divisor_kernel_prime_power _ q.property]
  simp_rw [lemma162_odd_kernel_raw_eq χ β hβ γ hγ hB q hq]
  rw [← sum_div,lemma162_raw_kernel_sum]
  unfold lemma162RawPrimeCoefficient
  ring

lemma lemma162_two_prime_power_raw_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (n : ℕ) :
    lemma162TwoCoefficientArithmetic χ β γ (2^n) =
      lemma162RawPrimeCoefficient χ β γ lemma162PrimeTwo n /
        lemma162TwoNormalizer χ β (1-γ) := by
  simp only [lemma162TwoCoefficientArithmetic,ArithmeticFunction.pmul_apply,lemma162_prime_power_part_apply]
  rw [lemma162_nu_chi_prime_power_h3 χ Nat.prime_two,lemma162_divisor_kernel_prime_power _ Nat.prime_two]
  simp_rw [lemma162_two_kernel_raw_eq χ β γ]
  rw [← sum_div,lemma162_raw_kernel_sum]
  unfold lemma162RawPrimeCoefficient lemma162PrimeTwo
  rw [div_mul_eq_mul_div]
  rfl

/-- Pointwise source-local equality, including the q=2 degree-zero term. -/
lemma lemma162_actual_local_series_eq_raw {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (q : Nat.Primes) (s : ℂ) :
    lemma162ActualLocalSeries χ β γ q s =
      ∑' n : ℕ, (lemma162RawPrimeCoefficient χ β γ q n / lemma162LocalNormalizer χ β γ q)*
        lemma32PrimeMonomial q.val s^n := by
  have hB := (lemma162_odd_baseline_nonzero χ β hβ (1-γ) (by simp [hγ]; norm_num) hstar).1
  by_cases hq : q=lemma162PrimeTwo
  · subst q
    simp only [lemma162ActualLocalSeries,lemma162LocalNormalizer]
    apply tsum_congr
    intro n
    rw [lemma162_two_prime_power_raw_eq]
    rfl
  · have hp : 2<q.val := by
      have htwo := q.property.two_le
      have hn : q.val≠2 := fun h => hq (Subtype.ext h)
      omega
    simp only [lemma162ActualLocalSeries,lemma162LocalNormalizer,if_neg hq]
    apply tsum_congr
    intro n
    rw [lemma162_odd_prime_power_raw_eq χ β hβ γ hγ hB q hp]

end ZhangLS.Spec
