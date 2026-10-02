import ZhangLS.Spec.Lemma162OddVarpi
import ZhangLS.Spec.Lemma162PrimeSupportedConvolution

/-! Exact exceptional-prime reassembly for the ORIGINAL Section16 varpi.
Neither varpi(1)=1 nor multiplicativity of raw varpi is assumed. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_odd_m_remove_two_powers {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β s : ℂ) (i j d l : ℕ) :
    lemma162OddMEulerProduct χ β (2^i*d) (2^j*l) s = lemma162OddMEulerProduct χ β d l s := by
  unfold lemma162OddMEulerProduct
  apply tprod_congr
  intro q
  unfold lemma162OddMPrimeFactor
  by_cases hq : 2<q.val
  · rw [if_pos hq,if_pos hq]
    have hn : ¬ q.val ∣ 2 := by
      intro h
      rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
      · exact q.property.ne_one h
      · omega
    have hi : ¬q.val ∣ 2^i := fun h => hn (q.property.dvd_of_dvd_pow h)
    have hj : ¬q.val ∣ 2^j := fun h => hn (q.property.dvd_of_dvd_pow h)
    simp only [lemma162GeneralMPrimeFactor,q.property.dvd_mul,hi,hj,false_or]
  · simp only [if_neg hq]

lemma lemma162_m_two_remove_odd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β s : ℂ) (i j d l : ℕ) (hcop : (2:ℕ).Coprime (d*l)) :
    lemma162GeneralMPrimeFactor χ β (2^i*d) (2^j*l) lemma162PrimeTwo s =
      lemma162GeneralMPrimeFactor χ β (2^i) (2^j) lemma162PrimeTwo s := by
  have hc : (2:ℕ).Coprime d ∧ (2:ℕ).Coprime l := Nat.coprime_mul_iff_right.mp hcop
  have hd : ¬2∣d := Nat.prime_two.coprime_iff_not_dvd.mp hc.1
  have hl : ¬2∣l := Nat.prime_two.coprime_iff_not_dvd.mp hc.2
  simp only [lemma162GeneralMPrimeFactor,lemma162PrimeTwo,Nat.prime_two.dvd_mul,hd,hl,or_false]

noncomputable def lemma162ActualVarpiKernel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (d l : ℕ) : ℂ :=
  lemma161Lambda χ β d*(d:ℂ)^γ*χ.evalNat l *
    (lemma162GeneralMEulerProduct χ β d l (1-γ)/lemma161Star χ β (1-γ))

noncomputable def lemma162TwoVarpiKernel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (d l : ℕ) : ℂ :=
  lemma161Lambda χ β d*(d:ℂ)^γ*χ.evalNat l *
    (lemma162GeneralMPrimeFactor χ β d l lemma162PrimeTwo (1-γ)/
      lemma162TwoNormalizer χ β (1-γ))

lemma lemma162_actual_kernel_two_odd_split {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0)
    (i j d l : ℕ) (hcop : (2:ℕ).Coprime (d*l)) :
    lemma162ActualVarpiKernel χ β γ (2^i*d) (2^j*l) =
      lemma162TwoVarpiKernel χ β γ (2^i) (2^j) * lemma162OddVarpiKernel χ β γ d l := by
  have hc : (2:ℕ).Coprime d ∧ (2:ℕ).Coprime l := Nat.coprime_mul_iff_right.mp hcop
  have hd : d ≠ 0 := by intro h; rw [h,zero_mul] at hcop; norm_num at hcop
  have hl : l ≠ 0 := by intro h; rw [h,mul_zero] at hcop; norm_num at hcop
  have hi : (2:ℕ)^i ≠ 0 := pow_ne_zero i (by norm_num)
  have hj : (2:ℕ)^j ≠ 0 := pow_ne_zero j (by norm_num)
  have hs : 9/10 ≤ (1-γ).re := by simp [hγ]; norm_num
  obtain ⟨hB,hN⟩ := lemma162_odd_baseline_nonzero χ β hβ (1-γ) hs hstar
  unfold lemma162ActualVarpiKernel lemma162TwoVarpiKernel lemma162OddVarpiKernel
  rw [lemma162_general_m_two_odd_decomposition χ β hβ (mul_ne_zero hi hd) (mul_ne_zero hj hl) (1-γ) hs,
    lemma162_odd_m_remove_two_powers,lemma162_m_two_remove_odd χ β (1-γ) i j d l hcop,
    lemma162_star_odd_decomposition χ β hβ (1-γ) hs,
    lemma162_lambda_mul χ β hi hd (Nat.Coprime.pow_left i hc.1),
    Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  simp only [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
  field_simp

noncomputable def lemma162ActualCoefficientArithmetic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) : ArithmeticFunction ℂ :=
  (lemma152DivisorKernelSum (lemma162ActualVarpiKernel χ β γ)).pmul (lemma162NuChi χ)

lemma lemma162_actual_coefficient_arithmetic_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (n : ℕ) :
    lemma162ActualCoefficientArithmetic χ β γ n =
      lemma162Coefficient χ β γ (lemma162GeneralMEulerProduct χ β) n := rfl

noncomputable def lemma162TwoCoefficientArithmetic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) : ArithmeticFunction ℂ :=
  (lemma162PrimePowerPart 2 (lemma152DivisorKernelSum (lemma162TwoVarpiKernel χ β γ))).pmul
    (lemma162NuChi χ)

/-- Every actual coefficient, including its exceptional degree-zero term,
is exactly recovered. The two-adic factor is not required to be multiplicative. -/
lemma lemma162_actual_coefficient_reassembly {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) :
    lemma162ActualCoefficientArithmetic χ β γ =
      lemma162TwoCoefficientArithmetic χ β γ * lemma162OddCoefficientArithmetic χ β γ := by
  have he := lemma162_weighted_divisor_kernel_prime_convolution Nat.prime_two
    (lemma162ActualVarpiKernel χ β γ) (lemma162TwoVarpiKernel χ β γ)
    (lemma162OddVarpiKernel χ β γ)
    (lemma162_actual_kernel_two_odd_split χ β hβ γ hγ hstar)
    (lemma162NuChi χ) (lemma162_nu_chi_multiplicative χ)
  rw [lemma162ActualCoefficientArithmetic,he]
  congr 1
  ext n
  simp only [ArithmeticFunction.pmul_apply,lemma162CoprimePart,ArithmeticFunction.coe_mk,
    lemma162OddCoefficientArithmetic,lemma162OddRestriction,lemma162OddVarpiArithmetic]
  by_cases hn : n.Coprime 2
  · rw [if_pos hn.symm,if_pos hn]
  · have hn' : ¬(2:ℕ).Coprime n := fun h => hn h.symm
    rw [if_neg hn',if_neg hn,zero_mul]

end ZhangLS.Spec
