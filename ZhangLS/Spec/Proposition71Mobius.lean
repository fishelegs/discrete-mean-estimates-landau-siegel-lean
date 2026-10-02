import ZhangLS.Spec.Lemma83Definitions

/-! # Exact Möbius inversion in the finite Section 7 arithmetic sums -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset ArithmeticFunction
open scoped Classical
set_option maxHeartbeats 2000000

/-- The exact coprimality indicator used before (7.21). -/
theorem proposition71_mobius_coprime_indicator (k l : ℕ) :
    (∑ r ∈ (Nat.gcd k l).divisors, (ArithmeticFunction.moebius r : ℂ)) =
      if k.Coprime l then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd k l))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  change ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (Nat.gcd k l) = _ at h
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa only [ArithmeticFunction.one_apply,ArithmeticFunction.intCoe_apply,Nat.Coprime] using h

/-- Möbius inversion of a genuine finite coprimality-restricted sum. -/
theorem proposition71_mobius_insert (K : Finset ℕ) (k : ℕ) (f : ℕ → ℂ) :
    (∑ l ∈ K.filter (fun l => l.Coprime k), f l) =
      ∑ l ∈ K, f l * ∑ r ∈ (Nat.gcd k l).divisors,
        (ArithmeticFunction.moebius r : ℂ) := by
  simp_rw [proposition71_mobius_coprime_indicator]
  rw [sum_filter]
  apply sum_congr rfl
  intro l hl
  by_cases h : k.Coprime l <;> simp [h,Nat.coprime_comm]

/-- The Möbius factor on the coprime branch after k=rk₁. -/
theorem proposition71_mobius_coprime_factor {r k : ℕ} (h : r.Coprime k) :
    ArithmeticFunction.moebius (r*k) * ArithmeticFunction.moebius r =
      |ArithmeticFunction.moebius r| * ArithmeticFunction.moebius k := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
  have hs : ArithmeticFunction.moebius r * ArithmeticFunction.moebius r =
      |ArithmeticFunction.moebius r| := by
    rw [←pow_two,ArithmeticFunction.moebius_sq,ArithmeticFunction.abs_moebius]
  calc
    _ = (ArithmeticFunction.moebius r*ArithmeticFunction.moebius r)*
      ArithmeticFunction.moebius k := by ring
    _ = _ := by rw [hs]

/-- The noncoprime branch vanishes before any totient or complex-power
factorization is used. -/
theorem proposition71_mobius_factor_all (r k : ℕ) :
    ArithmeticFunction.moebius (r*k)*ArithmeticFunction.moebius r =
      if r.Coprime k then
        |ArithmeticFunction.moebius r| *ArithmeticFunction.moebius k else 0 := by
  split_ifs with h
  · exact proposition71_mobius_coprime_factor h
  · have hz : ArithmeticFunction.moebius (r*k) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun hsq => h (Nat.coprime_of_squarefree_mul hsq))
    rw [hz,zero_mul]

end ZhangLS.Spec
