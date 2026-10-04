import ZhangLS.Spec.CompositeRamanujanCenterArithmetic

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.CompositeRamanujanCenter
open Complex Finset
open scoped Classical ComplexConjugate

/-- Uniform averages descend through every surjective finite group map.
The proof averages translations twice, so no choice of fibre sizes is assumed. -/
theorem average_surjective {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : G →* H) (hπ : Function.Surjective π) (f : H → ℂ) :
    (∑ u : G, f (π u)) / (Fintype.card G : ℂ) =
      (∑ v : H, f v) / (Fintype.card H : ℂ) := by
  have hleft (v : H) : (∑ u : G, f (v * π u)) = ∑ u : G, f (π u) := by
    obtain ⟨w, rfl⟩ := hπ v
    exact Fintype.sum_bijective (fun u => w * u) (Group.mulLeft_bijective w)
      (fun u => f (π w * π u)) (fun u => f (π u)) (fun u => by simp only [map_mul])
  have hright (u : G) : (∑ v : H, f (v * π u)) = ∑ v : H, f v := by
    exact Fintype.sum_bijective (fun v => v * π u) (Group.mulRight_bijective (π u))
      (fun v => f (v * π u)) f (fun _ => rfl)
  have hcross : (Fintype.card H : ℂ) * (∑ u : G, f (π u)) =
      (Fintype.card G : ℂ) * (∑ v : H, f v) := by
    calc
      _ = ∑ v : H, ∑ u : G, f (v * π u) := by simp_rw [hleft]; simp
      _ = ∑ u : G, ∑ v : H, f (v * π u) := sum_comm
      _ = _ := by simp_rw [hright]; simp
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hH : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (div_eq_div_iff hG hH).mpr
  simpa only [mul_comm] using hcross

/-- Exact reduction of the actual unit average, even when d and k are not coprime. -/
theorem scaled_normalized_sum {d k : ℕ} [NeZero d] [NeZero k] (l : ℕ) :
    letI : NeZero (d * k) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne k)⟩
    ramanujanSum (d * k) (d * l) / ((d * k).totient : ℂ) =
      ramanujanSum k l / (k.totient : ℂ) := by
  letI : NeZero (d * k) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne k)⟩
  let π := ZMod.unitsMap (Nat.dvd_mul_left k d)
  have hphase (u : (ZMod (d * k))ˣ) :
      ZMod.stdAddChar (((d * l : ℕ) : ZMod (d * k)) * (u : ZMod (d * k))) =
        ZMod.stdAddChar ((l : ZMod k) * (π u : ZMod k)) := by
    calc
      _ = ZMod.stdAddChar ((d : ZMod (d * k)) *
          ((l : ZMod (d * k)) * (u : ZMod (d * k)))) := by
        congr 1
        push_cast
        ring
      _ = _ := by
        rw [fixedDGcd_additive_quotient, map_mul, map_natCast]
        rfl
  unfold ramanujanSum
  simp_rw [hphase]
  simpa only [ZMod.card_units_eq_totient] using
    average_surjective π (ZMod.unitsMap_surjective _)
      (fun v : (ZMod k)ˣ => ZMod.stdAddChar ((l : ZMod k) * (v : ZMod k)))

theorem ramanujanSum_coprime (A : ℕ) [NeZero A] (B : ℕ) (hB : B.Coprime A) :
    ramanujanSum A B = (ArithmeticFunction.moebius A : ℂ) := by
  rw [ramanujanSum_divisor_formula]
  simp [hB.symm.gcd_eq_one]

/-- Gcd normalization of the genuine Ramanujan center, also valid at B=0. -/
theorem normalized_gcd (A : ℕ) [NeZero A] (B : ℕ) :
    ramanujanSum A B / (A.totient : ℂ) =
      (ArithmeticFunction.moebius (A / Nat.gcd A B) : ℂ) /
        ((A / Nat.gcd A B).totient : ℂ) := by
  have hA := Nat.pos_of_ne_zero (NeZero.ne A)
  have hd := Nat.gcd_pos_of_pos_left B hA
  letI : NeZero (Nat.gcd A B) := ⟨hd.ne'⟩
  have hk := Nat.div_pos (Nat.le_of_dvd hA (Nat.gcd_dvd_left A B)) hd
  letI : NeZero (A / Nat.gcd A B) := ⟨hk.ne'⟩
  have hc : (B / Nat.gcd A B).Coprime (A / Nat.gcd A B) :=
    Nat.Coprime.symm (Nat.gcd_div_gcd_div_gcd_of_pos_left hA)
  have hs := scaled_normalized_sum (d := Nat.gcd A B) (k := A / Nat.gcd A B)
    (B / Nat.gcd A B)
  rw [ramanujanSum_coprime _ _ hc] at hs
  have hAd : Nat.gcd A B * (A / Nat.gcd A B) = A :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have hBd : Nat.gcd A B * (B / Nat.gcd A B) = B :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
  convert hs using 1
  simp only [hAd, hBd]

end ZhangLS.Spec.CompositeRamanujanCenter
