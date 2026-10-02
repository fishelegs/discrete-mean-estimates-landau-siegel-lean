import ZhangLS.Spec.Lemma152ModifiedMultiplicative
import ZhangLS.Spec.Lemma152DivisorKernel
import ZhangLS.Spec.Lemma152LocalSeries
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def lemma152XiWeight {D : ℕ} (χ : RealPrimitiveCharacter D)
    (l : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun k => if k.Coprime l then (ArithmeticFunction.moebius k:ℂ)*χ.evalNat k*
    (k:ℂ)/(Nat.totient k:ℂ) else 0,by simp⟩

lemma lemma152_xi_weight_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D) (l : ℕ) :
    (lemma152XiWeight χ l).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [lemma152XiWeight],?_⟩
  intro a b ha hb hab
  have hμ := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
  simp only [lemma152XiWeight,ArithmeticFunction.coe_mk,Nat.coprime_mul_iff_left]
  by_cases hal : a.Coprime l
  · by_cases hbl : b.Coprime l
    · simp only [if_pos hal,if_pos hbl,if_pos (And.intro hal hbl)]
      rw [hμ,Int.cast_mul,Nat.totient_mul hab,Nat.cast_mul,Nat.cast_mul]
      simp only [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
      ring
    · simp [hal,hbl]
  · by_cases hbl : b.Coprime l <;> simp [hal,hbl]

noncomputable def lemma152XiKernel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l a k : ℕ) : ℂ :=
  lemma152ModifiedKappa χ β a (d*k) 1 * lemma152XiWeight χ l k

@[simp] lemma lemma152_xi_kernel_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l : ℕ) : lemma152XiKernel χ β d l 1 1 = 1 := by
  simp [lemma152XiKernel,(lemma152_xi_weight_multiplicative χ l).map_one]

lemma lemma152_xi_kernel_mul {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (d l a k b r : ℕ) (h : (a*k).Coprime (b*r)) :
    lemma152XiKernel χ β d l (a*b) (k*r) =
      lemma152XiKernel χ β d l a k * lemma152XiKernel χ β d l b r := by
  by_cases hak : a*k = 0
  · have hbr : b*r = 1 := by simpa [hak] using h
    have hone : b = 1 ∧ r = 1 := by simpa using hbr
    obtain ⟨rfl,rfl⟩ := hone
    simp
  by_cases hbr : b*r = 0
  · have hak' : a*k = 1 := by simpa [hbr] using h
    have hone : a = 1 ∧ k = 1 := by simpa using hak'
    obtain ⟨rfl,rfl⟩ := hone
    simp
  have ha : a ≠ 0 := left_ne_zero_of_mul hak
  have hb : b ≠ 0 := left_ne_zero_of_mul hbr
  have hab : a.Coprime b := h.coprime_mul_right.coprime_mul_right_right
  have har : a.Coprime r := h.coprime_mul_right.coprime_mul_left_right
  have hbk : b.Coprime k := h.coprime_mul_left.coprime_mul_right_right.symm
  have hkr : k.Coprime r := h.coprime_mul_left.coprime_mul_left_right
  have hma : lemma152ModifiedKappa χ β a (d*(k*r)) 1 =
      lemma152ModifiedKappa χ β a (d*k) 1 := by
    rw [← mul_assoc]
    exact lemma152_modified_kappa_exclusion_invariant χ β hβ ha har (d*k) _ (by norm_num)
  have hmb : lemma152ModifiedKappa χ β b (d*(k*r)) 1 =
      lemma152ModifiedKappa χ β b (d*r) 1 := by
    rw [show d*(k*r) = (d*r)*k by ring]
    exact lemma152_modified_kappa_exclusion_invariant χ β hβ hb hbk (d*r) _ (by norm_num)
  unfold lemma152XiKernel
  rw [lemma152_modified_kappa_mul χ β hβ ha hb hab _ _ (by norm_num),hma,hmb,
    (lemma152_xi_weight_multiplicative χ l).map_mul_of_coprime hkr]
  ring

lemma lemma152_xi_eq_kernel_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (n d l : ℕ) :
    lemma152Xi χ β n d l = lemma152DivisorKernelSum (lemma152XiKernel χ β d l) n := by
  unfold lemma152Xi lemma152DivisorKernelSum
  simp only [ArithmeticFunction.coe_mk]
  rw [sum_filter]
  apply sum_congr rfl
  intro a ha
  unfold lemma152XiKernel lemma152XiWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs <;> ring

noncomputable def lemma152CoefficientArithmetic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l : ℕ) : ArithmeticFunction ℂ :=
  ⟨lemma152Coefficient χ β d l,lemma152_coefficient_zero χ β d l⟩

/-- Multiplicativity of the actual Section 15 coefficient, with original d,l. -/
lemma lemma152_coefficient_multiplicative {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (d l : ℕ) :
    (lemma152CoefficientArithmetic χ β d l).IsMultiplicative := by
  have hk := lemma152_divisor_kernel_multiplicative (lemma152XiKernel χ β d l)
    (lemma152_xi_kernel_one χ β d l) (lemma152_xi_kernel_mul χ β hβ d l)
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨lemma152_coefficient_one χ β d l,?_⟩
  intro a b ha hb hab
  simp only [lemma152CoefficientArithmetic,ArithmeticFunction.coe_mk,lemma152Coefficient,
    lemma152_xi_eq_kernel_sum,lemma152_modified_lambda_mul χ β ha hb hab,
    hk.map_mul_of_coprime hab]
  ring

end ZhangLS.Spec
