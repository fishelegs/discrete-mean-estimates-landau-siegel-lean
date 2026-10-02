import ZhangLS.Spec.Lemma83ModifiedKappaMultiplicative
import ZhangLS.Spec.Lemma152DivisorKernel
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 500000

noncomputable def lemma83XiWeight (β : ℂ) (r : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun k => if k.Coprime r then (ArithmeticFunction.moebius k:ℂ) *
    (k:ℂ)^(1-β)/(Nat.totient k:ℂ) else 0,by simp⟩

lemma lemma83_xi_weight_multiplicative (β : ℂ) (r : ℕ) :
    (lemma83XiWeight β r).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [lemma83XiWeight],?_⟩
  intro a b ha hb hab
  have hμ := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
  simp only [lemma83XiWeight,ArithmeticFunction.coe_mk,Nat.coprime_mul_iff_left]
  by_cases har : a.Coprime r
  · by_cases hbr : b.Coprime r
    · simp only [if_pos har,if_pos hbr,if_pos (And.intro har hbr)]
      rw [hμ,Int.cast_mul,Nat.totient_mul hab,Nat.cast_mul,Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow]
      ring
    · simp [har,hbr]
  · by_cases hbr : b.Coprime r <;> simp [har,hbr]

noncomputable def lemma83XiKernel (β : Fin 3 → ℂ) (j : Fin 3) (d r a k : ℕ) : ℂ :=
  lemma83ModifiedKappa β a (d*r*k) (1-β j) * lemma83XiWeight (β j) r k

@[simp] lemma lemma83_xi_kernel_one (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) :
    lemma83XiKernel β j d r 1 1 = 1 := by
  simp [lemma83XiKernel,(lemma83_xi_weight_multiplicative (β j) r).map_one]

lemma lemma83_xi_kernel_mul (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) (d r a k b l : ℕ) (h : (a*k).Coprime (b*l)) :
    lemma83XiKernel β j d r (a*b) (k*l) =
      lemma83XiKernel β j d r a k * lemma83XiKernel β j d r b l := by
  by_cases hak : a*k = 0
  · have hbl : b*l = 1 := by simpa [hak] using h
    have hone : b = 1 ∧ l = 1 := by simpa using hbl
    obtain ⟨rfl,rfl⟩ := hone
    simp
  by_cases hbl : b*l = 0
  · have hak' : a*k = 1 := by simpa [hbl] using h
    have hone : a = 1 ∧ k = 1 := by simpa using hak'
    obtain ⟨rfl,rfl⟩ := hone
    simp
  have ha : a ≠ 0 := left_ne_zero_of_mul hak
  have hb : b ≠ 0 := left_ne_zero_of_mul hbl
  have hab : a.Coprime b := h.coprime_mul_right.coprime_mul_right_right
  have hal : a.Coprime l := h.coprime_mul_right.coprime_mul_left_right
  have hbk : b.Coprime k := h.coprime_mul_left.coprime_mul_right_right.symm
  have hkl : k.Coprime l := h.coprime_mul_left.coprime_mul_left_right
  have hs : 0 < (1-β j).re := by simp [hβ j]
  have hma : lemma83ModifiedKappa β a (d*r*(k*l)) (1-β j) =
      lemma83ModifiedKappa β a (d*r*k) (1-β j) := by
    rw [← mul_assoc]
    exact lemma83_modified_kappa_exclusion_invariant β hβ ha hal (d*r*k) _ hs
  have hmb : lemma83ModifiedKappa β b (d*r*(k*l)) (1-β j) =
      lemma83ModifiedKappa β b (d*r*l) (1-β j) := by
    rw [show d*r*(k*l) = (d*r*l)*k by ring]
    exact lemma83_modified_kappa_exclusion_invariant β hβ hb hbk (d*r*l) _ hs
  unfold lemma83XiKernel
  rw [lemma83_modified_kappa_mul β hβ ha hb hab _ _ hs,hma,hmb,
    (lemma83_xi_weight_multiplicative (β j) r).map_mul_of_coprime hkl]
  ring

lemma lemma83_xi_eq_kernel_sum (β : Fin 3 → ℂ) (j : Fin 3) (n d r : ℕ) :
    lemma83Xi β j n d r = lemma83ModifiedLambda β j n (d*r) *
      lemma152DivisorKernelSum (lemma83XiKernel β j d r) n := by
  unfold lemma83Xi lemma152DivisorKernelSum
  simp only [ArithmeticFunction.coe_mk]
  congr 1
  rw [sum_filter]
  apply sum_congr rfl
  intro a ha
  unfold lemma83XiKernel lemma83XiWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs <;> ring

/-- Actual ξ, as an arithmetic function; the divisor-sum definition is retained. -/
noncomputable def lemma83XiArithmetic (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) :
    ArithmeticFunction ℂ := ⟨fun n => lemma83Xi β j n d r,lemma83_xi_zero β j d r⟩

lemma lemma83_xi_multiplicative (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) (d r : ℕ) : (lemma83XiArithmetic β j d r).IsMultiplicative := by
  have hk := lemma152_divisor_kernel_multiplicative (lemma83XiKernel β j d r)
    (lemma83_xi_kernel_one β j d r) (lemma83_xi_kernel_mul β hβ j d r)
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [lemma83XiArithmetic],?_⟩
  intro a b ha hb hab
  simp only [lemma83XiArithmetic,ArithmeticFunction.coe_mk,lemma83_xi_eq_kernel_sum,
    lemma83_modified_lambda_mul β j ha hb hab,hk.map_mul_of_coprime hab]
  ring

end ZhangLS.Spec
