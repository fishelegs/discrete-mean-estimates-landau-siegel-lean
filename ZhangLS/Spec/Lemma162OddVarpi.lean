import ZhangLS.Spec.Lemma162OddM
import ZhangLS.Spec.Lemma162NuChi
import ZhangLS.Spec.Lemma152DivisorKernel

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_lambda_mul {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ)
    {d d' : ℕ} (hd : d ≠ 0) (hd' : d' ≠ 0) (h : d.Coprime d') :
    lemma161Lambda χ β (d*d') = lemma161Lambda χ β d*lemma161Lambda χ β d' := by
  unfold lemma161Lambda
  rw [Nat.primeFactors_mul hd hd',prod_union h.disjoint_primeFactors]

noncomputable def lemma162OddVarpiKernel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (d l : ℕ) : ℂ :=
  lemma161Lambda χ β d*(d:ℂ)^γ*χ.evalNat l *
    (lemma162OddMEulerProduct χ β d l (1-γ)/lemma162OddMEulerProduct χ β 1 1 (1-γ))

lemma lemma162_odd_varpi_kernel_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0) :
    lemma162OddVarpiKernel χ β γ 1 1 = 1 := by
  simp [lemma162OddVarpiKernel,RealPrimitiveCharacter.evalNat,hB]

lemma lemma162_odd_varpi_kernel_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0)
    (d l d' l' : ℕ) (h : (d*l).Coprime (d'*l')) :
    lemma162OddVarpiKernel χ β γ (d*d') (l*l') =
      lemma162OddVarpiKernel χ β γ d l * lemma162OddVarpiKernel χ β γ d' l' := by
  by_cases hdl : d*l = 0
  · have hone : d'=1 ∧ l'=1 := by
      have hh : d'*l'=1 := by simpa [hdl] using h
      simpa using hh
    obtain ⟨rfl,rfl⟩ := hone
    simp [lemma162_odd_varpi_kernel_one χ β γ hB]
  by_cases hdl' : d'*l'=0
  · have hone : d=1 ∧ l=1 := by
      have hh : d*l=1 := by simpa [hdl'] using h
      simpa using hh
    obtain ⟨rfl,rfl⟩ := hone
    simp [lemma162_odd_varpi_kernel_one χ β γ hB]
  have hd := left_ne_zero_of_mul hdl
  have hl := right_ne_zero_of_mul hdl
  have hd' := left_ne_zero_of_mul hdl'
  have hl' := right_ne_zero_of_mul hdl'
  unfold lemma162OddVarpiKernel
  rw [lemma162_lambda_mul χ β hd hd' h.coprime_mul_right.coprime_mul_right_right,
    Nat.cast_mul,Complex.natCast_mul_natCast_cpow,
    lemma162_odd_m_normalized_pair_mul χ β hβ hd hl hd' hl' h (1-γ)
      (by simp [hγ]; norm_num) hB]
  simp only [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
  ring

noncomputable def lemma162OddVarpiArithmetic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) : ArithmeticFunction ℂ :=
  lemma152DivisorKernelSum (lemma162OddVarpiKernel χ β γ)

lemma lemma162_odd_varpi_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0) :
    (lemma162OddVarpiArithmetic χ β γ).IsMultiplicative :=
  lemma152_divisor_kernel_multiplicative (lemma162OddVarpiKernel χ β γ)
    (lemma162_odd_varpi_kernel_one χ β γ hB)
    (lemma162_odd_varpi_kernel_mul χ β hβ γ hγ hB)

noncomputable def lemma162OddRestriction (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Coprime 2 then f n else 0,by simp⟩

lemma lemma162_odd_restriction_multiplicative (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) : (lemma162OddRestriction f).IsMultiplicative := by
  refine ⟨by simp [lemma162OddRestriction,hf.map_one],?_⟩
  intro m n hmn
  change (if (m*n).Coprime 2 then f (m*n) else 0) =
    (if m.Coprime 2 then f m else 0)*(if n.Coprime 2 then f n else 0)
  rw [hf.map_mul_of_coprime hmn]
  by_cases hm : m.Coprime 2
  · by_cases hn : n.Coprime 2
    · have hh : (m*n).Coprime 2 := Nat.coprime_mul_iff_left.mpr ⟨hm,hn⟩
      rw [if_pos hh,if_pos hm,if_pos hn]
    · have hh : ¬(m*n).Coprime 2 := fun h => hn (Nat.coprime_mul_iff_left.mp h).2
      rw [if_neg hh,if_pos hm,if_neg hn,mul_zero]
  · have hh : ¬(m*n).Coprime 2 := fun h => hm (Nat.coprime_mul_iff_left.mp h).1
    rw [if_neg hh,if_neg hm,zero_mul]

lemma lemma162_nu_chi_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (lemma162NuChi χ).IsMultiplicative :=
  (lemma31_actual_nu_multiplicative χ).mul χ.chi.isMultiplicative_toArithmeticFunction

noncomputable def lemma162OddCoefficientArithmetic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) : ArithmeticFunction ℂ :=
  lemma162OddRestriction ((lemma162OddVarpiArithmetic χ β γ).pmul (lemma162NuChi χ))

lemma lemma162_odd_coefficient_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (hB : lemma162OddMEulerProduct χ β 1 1 (1-γ) ≠ 0) :
    (lemma162OddCoefficientArithmetic χ β γ).IsMultiplicative :=
  lemma162_odd_restriction_multiplicative _
    ((lemma162_odd_varpi_multiplicative χ β hβ γ hγ hB).pmul
      (lemma162_nu_chi_multiplicative χ))

end ZhangLS.Spec
