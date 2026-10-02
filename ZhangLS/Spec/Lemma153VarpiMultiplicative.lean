import ZhangLS.Spec.Lemma153GeneralMRatio
import ZhangLS.Spec.Lemma153PrimePowerBridge
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma153_general_m_prime_pair_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l d' l' : ℕ) (h : (d*l).Coprime (d'*l'))
    (q : Nat.Primes) (s : ℂ) :
    lemma153GeneralMPrimeFactor χ β (d*d') (l*l') q s * lemma152PrimeFactor χ β q s =
      lemma153GeneralMPrimeFactor χ β d l q s * lemma153GeneralMPrimeFactor χ β d' l' q s := by
  by_cases hq : q.val ∣ d*l
  · have hq' : ¬q.val ∣ d'*l' := fun hh => q.property.ne_one (Nat.eq_one_of_dvd_coprimes h hq hh)
    have hd' : ¬q.val ∣ d' := fun hh => hq' (hh.trans (dvd_mul_right d' l'))
    have hl' : ¬q.val ∣ l' := fun hh => hq' (hh.trans (dvd_mul_left l' d'))
    simp [lemma153GeneralMPrimeFactor,q.property.dvd_mul,hd',hl']
  · have hd : ¬q.val ∣ d := fun hh => hq (hh.trans (dvd_mul_right d l))
    have hl : ¬q.val ∣ l := fun hh => hq (hh.trans (dvd_mul_left l d))
    simp [lemma153GeneralMPrimeFactor,q.property.dvd_mul,hd,hl,mul_comm]

lemma lemma153_general_m_pair_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0)
    {d l d' l' : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) (hd' : d' ≠ 0) (hl' : l' ≠ 0)
    (h : (d*l).Coprime (d'*l')) (s : ℂ) (hs : 9/10 ≤ s.re) :
    lemma153GeneralMEulerProduct χ β (d*d') (l*l') s * lemma152EulerProduct χ β s =
      lemma153GeneralMEulerProduct χ β d l s * lemma153GeneralMEulerProduct χ β d' l' s := by
  have ha := (lemma153_general_m_euler_multipliable χ β hβ (mul_ne_zero hd hd') (mul_ne_zero hl hl') s hs).hasProd
  have hb := (lemma152_euler_product_multipliable χ β hβ s hs).hasProd
  have hc := (lemma153_general_m_euler_multipliable χ β hβ hd hl s hs).hasProd
  have he := (lemma153_general_m_euler_multipliable χ β hβ hd' hl' s hs).hasProd
  exact ((ha.mul hb).congr_fun (fun q => (lemma153_general_m_prime_pair_mul χ β d l d' l' h q s).symm)).unique (hc.mul he)

lemma lemma153_general_m_normalized_pair_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0)
    {d l d' l' : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) (hd' : d' ≠ 0) (hl' : l' ≠ 0)
    (h : (d*l).Coprime (d'*l')) (s : ℂ) (hs : 9/10 ≤ s.re)
    (hM : lemma152EulerProduct χ β s ≠ 0) :
    lemma153GeneralMEulerProduct χ β (d*d') (l*l') s / lemma153GeneralMEulerProduct χ β 1 1 s =
      (lemma153GeneralMEulerProduct χ β d l s / lemma153GeneralMEulerProduct χ β 1 1 s) *
        (lemma153GeneralMEulerProduct χ β d' l' s / lemma153GeneralMEulerProduct χ β 1 1 s) := by
  simp only [lemma153_general_m_baseline]
  have hh := lemma153_general_m_pair_mul χ β hβ hd hl hd' hl' h s hs
  field_simp
  exact hh

lemma lemma153_lambda_mul {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ)
    {d d' : ℕ} (hd : d ≠ 0) (hd' : d' ≠ 0) (h : d.Coprime d') :
    lemma152Lambda χ β (d*d') = lemma152Lambda χ β d*lemma152Lambda χ β d' := by
  unfold lemma152Lambda
  rw [Nat.primeFactors_mul hd hd',prod_union h.disjoint_primeFactors]

noncomputable def lemma153ActualVarpiKernel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (d l : ℕ) : ℂ :=
  lemma152Lambda χ β d*(d:ℂ)^γ*χ.evalNat l *
    (lemma153GeneralMEulerProduct χ β d l (1-γ)/lemma153GeneralMEulerProduct χ β 1 1 (1-γ))

lemma lemma153_actual_varpi_kernel_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) :
    lemma153ActualVarpiKernel χ β γ 1 1 = 1 := by
  simp [lemma153ActualVarpiKernel,RealPrimitiveCharacter.evalNat,hM]

lemma lemma153_actual_varpi_kernel_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0)
    (d l d' l' : ℕ) (h : (d*l).Coprime (d'*l')) :
    lemma153ActualVarpiKernel χ β γ (d*d') (l*l') =
      lemma153ActualVarpiKernel χ β γ d l * lemma153ActualVarpiKernel χ β γ d' l' := by
  by_cases hdl : d*l = 0
  · have hone : d'=1 ∧ l'=1 := by
      have hh : d'*l'=1 := by simpa [hdl] using h
      simpa using hh
    obtain ⟨rfl,rfl⟩ := hone
    simp [lemma153_actual_varpi_kernel_one χ β γ hM]
  by_cases hdl' : d'*l'=0
  · have hone : d=1 ∧ l=1 := by
      have hh : d*l=1 := by simpa [hdl'] using h
      simpa using hh
    obtain ⟨rfl,rfl⟩ := hone
    simp [lemma153_actual_varpi_kernel_one χ β γ hM]
  have hd := left_ne_zero_of_mul hdl
  have hl := right_ne_zero_of_mul hdl
  have hd' := left_ne_zero_of_mul hdl'
  have hl' := right_ne_zero_of_mul hdl'
  unfold lemma153ActualVarpiKernel
  rw [lemma153_lambda_mul χ β hd hd' h.coprime_mul_right.coprime_mul_right_right,
    Nat.cast_mul,Complex.natCast_mul_natCast_cpow,
    lemma153_general_m_normalized_pair_mul χ β hβ hd hl hd' hl' h (1-γ)
      (by simp [hγ]; norm_num) hM]
  simp only [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
  ring

noncomputable def lemma153ActualVarpiArithmetic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) : ArithmeticFunction ℂ :=
  lemma152DivisorKernelSum (lemma153ActualVarpiKernel χ β γ)

lemma lemma153_actual_varpi_arithmetic_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (n : ℕ) :
    lemma153ActualVarpiArithmetic χ β γ n =
      lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) n := rfl

lemma lemma153_actual_varpi_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) :
    (lemma153ActualVarpiArithmetic χ β γ).IsMultiplicative :=
  lemma152_divisor_kernel_multiplicative (lemma153ActualVarpiKernel χ β γ)
    (lemma153_actual_varpi_kernel_one χ β γ hM)
    (lemma153_actual_varpi_kernel_mul χ β hβ γ hγ hM)

noncomputable def lemma153ActualCoefficientArithmetic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) : ArithmeticFunction ℂ :=
  ⟨lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β),by
    simp [lemma153Coefficient,lemma153Varpi]⟩

/-- Multiplicativity of the actual χ(n)τ₂(n)varpi₁ⱼ(n) coefficient. -/
lemma lemma153_actual_coefficient_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) :
    (lemma153ActualCoefficientArithmetic χ β γ).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨?_,?_⟩
  · exact lemma153_coefficient_one χ β γ (lemma153GeneralMEulerProduct χ β)
      (by simpa using hM)
  · intro a b ha hb hab
    have hv := (lemma153_actual_varpi_multiplicative χ β hβ γ hγ hM).map_mul_of_coprime hab
    have ht := (lemma34_tau_multiplicative 2).map_mul_of_coprime hab
    change lemma34Tau 2 (a*b) = lemma34Tau 2 a*lemma34Tau 2 b at ht
    change lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) (a*b) =
      lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) a *
        lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) b at hv
    simp only [lemma153ActualCoefficientArithmetic,ArithmeticFunction.coe_mk,
      lemma153Coefficient,hv,ht,Nat.cast_mul,RealPrimitiveCharacter.evalNat,map_mul]
    ring

end ZhangLS.Spec
