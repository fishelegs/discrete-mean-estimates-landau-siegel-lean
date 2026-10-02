import ZhangLS.Spec.InducedGaussInflation

/-! # The genuine induced Gauss–Möbius formula

For every character χ modulo r and every h>0,
τ(changeLevel χ to r*h)=μ(h)χ(h)τ(χ).
Primitivity is not assumed here; it will only be used in the conductor norm
corollary. All finite reindexings include residue zero and the r=h=1 case.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

/-- Exact finite Möbius insertion for a coprimality-filtered sum. -/
theorem inducedGauss_coprime_sum_mobius {h : ℕ} (hh : h≠0) (M : ℕ) (f : ℕ → ℂ) :
    (∑ a ∈ range M, if a.Coprime h then f a else 0) =
      ∑ d ∈ h.divisors, (ArithmeticFunction.moebius d:ℂ)*
        ∑ a ∈ range M, if d∣a then f a else 0 := by
  have hp (a : ℕ) : (if a.Coprime h then f a else 0) =
      f a*∑ d ∈ h.divisors, if d∣a then (ArithmeticFunction.moebius d:ℂ) else 0 := by
    rw [inducedGauss_mobius_indicator_divisors hh a]
    by_cases hc : a.Coprime h <;> simp [hc]
  simp_rw [hp,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro a ha
  by_cases hda : d∣a <;> simp [hda,mul_comm]

/-- The actual divisibility-restricted residue sum after a=d*b.
The sole possible survivor is d=h. -/
theorem inducedGauss_divisor_inner {r h : ℕ} [NeZero r] [NeZero h]
    (χ : DirichletCharacter ℂ r) {d : ℕ} (hdh : d∣h) :
    letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
    (∑ a ∈ range (r*h), if d∣a then χ (a:ZMod r)*ZMod.stdAddChar (a:ZMod (r*h)) else 0) =
      if d=h then χ (d:ZMod r)*gaussSum χ ZMod.stdAddChar else 0 := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  have hhp : 0<h := Nat.pos_of_ne_zero (NeZero.ne h)
  have hdp : 0<d := Nat.pos_of_dvd_of_pos hdh hhp
  letI : NeZero d := ⟨hdp.ne'⟩
  let q := h/d
  have hqp : 0<q := Nat.div_pos (Nat.le_of_dvd hhp hdh) hdp
  letI : NeZero q := ⟨hqp.ne'⟩
  letI : NeZero (r*q) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne q)⟩
  have hdq : d*q=h := Nat.mul_div_cancel' hdh
  have hN : r*h=d*(r*q) := by rw [← hdq]; ring
  let f : ℕ → ℂ := fun a => χ (a:ZMod r)*ZMod.stdAddChar (a:ZMod (r*h))
  have hs : (∑ a ∈ range (r*h), if d∣a then f a else 0) =
      ∑ b ∈ range (r*q), f (d*b) := by
    calc
      _ = ∑ a ∈ range (d*(r*q)), if d∣a then f a else 0 := by rw [← hN]
      _ = _ := inducedGauss_sum_range_multiples hdp f
  have hphase (b : ℕ) : ZMod.stdAddChar ((d*b:ℕ):ZMod (r*h)) =
      ZMod.stdAddChar (b:ZMod (r*q)) := by
    have hleft := ZMod.stdAddChar_coe (N := r*h) ((d*b:ℕ):ℤ)
    have hright := ZMod.stdAddChar_coe (N := r*q) (b:ℤ)
    simp only [Int.cast_natCast] at hleft hright
    rw [hleft,hright]
    congr 1
    have hNC : (r:ℂ)*(h:ℂ)=(d:ℂ)*((r:ℂ)*(q:ℂ)) := by exact_mod_cast hN
    have hdC : (d:ℂ)≠0 := Nat.cast_ne_zero.mpr hdp.ne'
    have hrC : (r:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
    have hqC : (q:ℂ)≠0 := Nat.cast_ne_zero.mpr hqp.ne'
    push_cast
    rw [hNC]
    field_simp
  have hfactor : (∑ b ∈ range (r*q), f (d*b)) = χ (d:ZMod r)*inducedGaussInflation (h := q) χ := by
    unfold inducedGaussInflation
    rw [mul_sum]
    apply sum_congr rfl
    intro b hb
    dsimp [f]
    rw [hphase,Nat.cast_mul,map_mul]
    ring
  change (∑ a ∈ range (r*h), if d∣a then f a else 0) = _
  rw [hs,hfactor,inducedGauss_inflation_formula]
  have heq : q=1 ↔ d=h := by
    constructor
    · intro hq
      simpa only [hq,mul_one] using hdq
    · intro hd
      subst d
      exact Nat.div_self hhp
  by_cases he : d=h
  · rw [if_pos (heq.mpr he),if_pos he]
  · rw [if_neg (fun hq => he (heq.mp hq)),if_neg he,mul_zero]

/-- Exact Gauss sum after induction to any positive multiple of its modulus. -/
theorem inducedGauss_changeLevel_formula {r h : ℕ} [NeZero r] [NeZero h]
    (χ : DirichletCharacter ℂ r) :
    letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
    gaussSum (χ.changeLevel (r.dvd_mul_right h)) ZMod.stdAddChar =
      (ArithmeticFunction.moebius h:ℂ)*χ (h:ZMod r)*gaussSum χ ZMod.stdAddChar := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  rw [gaussSum,inducedGauss_sum_zmod_eq_range]
  have hpoint (a : ℕ) :
      χ.changeLevel (r.dvd_mul_right h) (a:ZMod (r*h))*ZMod.stdAddChar (a:ZMod (r*h)) =
        if a.Coprime h then χ (a:ZMod r)*ZMod.stdAddChar (a:ZMod (r*h)) else 0 := by
    rw [inducedGauss_changeLevel_nat]
    by_cases ha : a.Coprime h <;> simp [ha]
  simp_rw [hpoint]
  rw [inducedGauss_coprime_sum_mobius (NeZero.ne h)]
  calc
    _ = ∑ d ∈ h.divisors, if d=h then
        (ArithmeticFunction.moebius d:ℂ)*χ (d:ZMod r)*gaussSum χ ZMod.stdAddChar else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [inducedGauss_divisor_inner χ (Nat.mem_divisors.mp hd).1]
      by_cases he : d=h <;> simp [he,mul_assoc]
    _ = _ := by simp [Nat.mem_divisors,NeZero.ne h]

end ZhangLS.Spec
