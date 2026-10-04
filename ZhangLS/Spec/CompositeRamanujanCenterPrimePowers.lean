import ZhangLS.Spec.CompositeRamanujanCenterExpansion

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.CompositeRamanujanCenter
open Complex Finset
open scoped Classical ComplexConjugate

/-- Full divisibility gives the actual number of units. -/
theorem ramanujanSum_divisible (A : ℕ) [NeZero A] (B : ℕ) (hAB : A ∣ B) :
    ramanujanSum A B = (A.totient : ℂ) := by
  have hB : (B : ZMod A) = 0 := (ZMod.natCast_eq_zero_iff B A).mpr hAB
  simp [ramanujanSum, hB, ZMod.card_units_eq_totient]

/-- The prime-power middle branch, with every coprime reduced numerator. -/
theorem prime_power_middle {q : ℕ} (hq : q.Prime) (r l : ℕ) (hl : l.Coprime q) :
    letI : NeZero q := ⟨hq.ne_zero⟩
    ramanujanSum (q ^ (r + 1)) (q ^ r * l) = -(q ^ r : ℂ) := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  letI : NeZero (q ^ r) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have hs := scaled_normalized_sum (d := q ^ r) (k := q) l
  rw [ramanujanSum_coprime q l hl, ArithmeticFunction.moebius_apply_prime hq] at hs
  have hphi : (q ^ r * q).totient = q ^ r * q.totient := by
    rw [← pow_succ, Nat.totient_prime_pow_succ hq, Nat.totient_prime hq]
  have hqC : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq.pos).ne'
  have hN : ((q ^ r * q).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (pow_pos hq.pos _) hq.pos)).ne'
  have he := (div_eq_div_iff hN hqC).mp hs
  rw [hphi, Nat.cast_mul, Nat.cast_pow, Int.cast_neg, Int.cast_one] at he
  have hh : ramanujanSum (q ^ r * q) (q ^ r * l) = -(q ^ r : ℂ) := by
    apply mul_right_cancel₀ hqC
    calc
      _ = (-1 : ℂ) * ((q ^ r : ℂ) * (q.totient : ℂ)) := he
      _ = _ := by ring
  simpa only [pow_succ] using hh

/-- A numerator coprime to q has zero Ramanujan sum at every q-power ≥q². -/
theorem prime_power_coprime_zero {q : ℕ} (hq : q.Prime) (r B : ℕ)
    (hB : B.Coprime q) :
    letI : NeZero q := ⟨hq.ne_zero⟩
    ramanujanSum (q ^ (r + 2)) B = 0 := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  rw [ramanujanSum_coprime _ B (hB.pow_right _),
    ArithmeticFunction.moebius_apply_prime_pow hq (by omega), if_neg (by omega)]
  simp

end ZhangLS.Spec.CompositeRamanujanCenter
