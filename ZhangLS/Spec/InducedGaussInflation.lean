import ZhangLS.Spec.InducedGaussFiniteSums

/-! # Cancellation of an actual periodic-character Gauss inflation

Translation by r kills the sum at modulus r*h when h>1. This requires no
primitivity, and leaves the h=1 / modulus-one branch explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

noncomputable def inducedGaussInflation {r h : ℕ} [NeZero r] [NeZero h]
    (χ : DirichletCharacter ℂ r) : ℂ :=
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  ∑ b ∈ range (r*h), χ (b:ZMod r)*ZMod.stdAddChar (b:ZMod (r*h))

/-- The nontrivial inflation vanishes by an actual residue permutation. -/
theorem inducedGauss_inflation_zero {r h : ℕ} [NeZero r] [NeZero h]
    (χ : DirichletCharacter ℂ r) (hh : 1<h) : inducedGaussInflation (h := h) χ=0 := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  let π := ZMod.castHom (r.dvd_mul_right h) (ZMod r)
  let f : ZMod (r*h) → ℂ := fun a => χ (π a)*ZMod.stdAddChar a
  have heq : inducedGaussInflation (h := h) χ=∑ a : ZMod (r*h), f a := by
    rw [inducedGauss_sum_zmod_eq_range]
    simp only [inducedGaussInflation,f,π,map_natCast]
  have hp : π (r:ZMod (r*h))=0 := by simp [π]
  have ht (a : ZMod (r*h)) : f (a+(r:ZMod (r*h)))=
      ZMod.stdAddChar (r:ZMod (r*h))*f a := by
    dsimp [f]
    rw [map_add,hp,add_zero,AddChar.map_add_eq_mul]
    ring
  have hs : (∑ a : ZMod (r*h), f (a+(r:ZMod (r*h))))=∑ a : ZMod (r*h), f a :=
    Fintype.sum_equiv (Equiv.addRight (r:ZMod (r*h))) _ _ (fun _ => rfl)
  simp_rw [ht] at hs
  rw [← mul_sum] at hs
  have hrp : 0<r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hrh : r<r*h := by nlinarith
  have hrzero : (r:ZMod (r*h))≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff r (r*h)).mp hz
    exact (not_le_of_gt hrh) (Nat.le_of_dvd hrp hd)
  have hphase : ZMod.stdAddChar (r:ZMod (r*h))≠1 := by
    intro hz
    apply hrzero
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using hz
  have hzero : (ZMod.stdAddChar (r:ZMod (r*h))-1)*(∑ a : ZMod (r*h), f a)=0 := by
    linear_combination hs
  have hz := (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hphase)
  exact heq.trans hz

/-- The only surviving periodic inflation is exactly the original Gauss sum. -/
theorem inducedGauss_inflation_one {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    inducedGaussInflation (h := 1) χ=gaussSum χ ZMod.stdAddChar := by
  unfold inducedGaussInflation gaussSum
  simp only [mul_one]
  rw [inducedGauss_sum_zmod_eq_range]
  apply sum_congr rfl
  intro b hb
  congr 1
  have hleft := ZMod.stdAddChar_coe (N := r*1) (b:ℤ)
  have hright := ZMod.stdAddChar_coe (N := r) (b:ℤ)
  simp only [Int.cast_natCast,Nat.cast_mul,Nat.cast_one,mul_one] at hleft hright
  rw [hleft,hright]

/-- General periodic cancellation, including the r=1 and h=1 cases. -/
theorem inducedGauss_inflation_formula {r h : ℕ} [NeZero r] [NeZero h]
    (χ : DirichletCharacter ℂ r) :
    inducedGaussInflation (h := h) χ = if h=1 then gaussSum χ ZMod.stdAddChar else 0 := by
  by_cases hh : h=1
  · subst h
    simp [inducedGauss_inflation_one]
  · rw [if_neg hh]
    exact inducedGauss_inflation_zero χ (by have := NeZero.ne h; omega)

end ZhangLS.Spec
