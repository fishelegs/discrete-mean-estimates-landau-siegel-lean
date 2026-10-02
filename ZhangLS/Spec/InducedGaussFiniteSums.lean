import ZhangLS.Spec.Lemma23PrimitiveGaussSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # Finite residue and Möbius identities for induced Gauss sums

All residues, including zero and modulus one, remain in the sums. The
multiples-of-d reindex is proved as a finite bijection.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

/-- Standard representatives, including residue zero, for a nonzero modulus. -/
theorem inducedGauss_sum_zmod_eq_range {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ a : ZMod N, f a) = ∑ a ∈ range N, f (a:ZMod N) := by
  apply sum_bij (fun a _ => a.val)
  · intro a ha
    exact mem_range.mpr (ZMod.val_lt a)
  · intro a ha b hb he
    exact ZMod.val_injective N he
  · intro a ha
    refine ⟨(a:ZMod N),mem_univ _,?_⟩
    exact ZMod.val_natCast_of_lt (mem_range.mp ha)
  · intro a ha
    rw [ZMod.natCast_zmod_val]

/-- Exact finite substitution a=d*b on the divisibility branch. -/
theorem inducedGauss_sum_range_multiples {d M : ℕ} (hd : 0<d) (f : ℕ → ℂ) :
    (∑ a ∈ range (d*M), if d∣a then f a else 0) = ∑ b ∈ range M, f (d*b) := by
  rw [← sum_filter]
  symm
  apply sum_bij (fun b _ => d*b)
  · intro b hb
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hd),dvd_mul_right d b⟩
  · intro a ha b hb he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro a ha
    obtain ⟨hRange,hdiv⟩ := mem_filter.mp ha
    obtain ⟨b,hb⟩ := hdiv
    refine ⟨b,mem_range.mpr ?_,hb.symm⟩
    have hh := mem_range.mp hRange
    rw [hb] at hh
    exact (Nat.mul_lt_mul_left hd).mp hh
  · intro b hb
    rfl

/-- Pointwise induction is a genuine coprimality indicator, not a false
all-naturals equality between induced and inducing characters. -/
theorem inducedGauss_changeLevel_nat {r h : ℕ} [NeZero r] [NeZero h]
    (χ : DirichletCharacter ℂ r) (a : ℕ) :
    χ.changeLevel (r.dvd_mul_right h) (a:ZMod (r*h)) =
      if a.Coprime h then χ (a:ZMod r) else 0 := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  by_cases hn : a.Coprime (r*h)
  · have har : a.Coprime r := hn.of_dvd_right (r.dvd_mul_right h)
    have hah : a.Coprime h := hn.of_dvd_right (h.dvd_mul_left r)
    rw [if_pos hah]
    have he := changeLevel_eq_cast_of_dvd χ (r.dvd_mul_right h) (ZMod.unitOfCoprime a hn)
    simpa only [ZMod.coe_unitOfCoprime,ZMod.cast_natCast (r.dvd_mul_right h) a] using he
  · rw [MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hn)]
    by_cases hah : a.Coprime h
    · rw [if_pos hah]
      have har : ¬a.Coprime r := fun hr => hn (hr.mul_right hah)
      exact (MulChar.map_nonunit χ (by simpa only [ZMod.isUnit_iff_coprime] using har)).symm
    · rw [if_neg hah]

/-- The exact Möbius coprimality indicator, including a=0. -/
theorem inducedGauss_mobius_indicator (h a : ℕ) :
    (∑ d ∈ (Nat.gcd h a).divisors, (ArithmeticFunction.moebius d:ℂ)) =
      if h.Coprime a then 1 else 0 := by
  have hh := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd h a))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  change ((ArithmeticFunction.moebius:ArithmeticFunction ℂ)*
    (ArithmeticFunction.zeta:ArithmeticFunction ℂ)) (Nat.gcd h a) = _ at hh
  rw [ArithmeticFunction.coe_mul_zeta_apply] at hh
  simpa only [ArithmeticFunction.one_apply,ArithmeticFunction.intCoe_apply,Nat.Coprime] using hh

/-- The gcd-divisor sum is a finite sum over d|h with the actual d|a test. -/
theorem inducedGauss_mobius_indicator_divisors {h : ℕ} (hh : h≠0) (a : ℕ) :
    (∑ d ∈ h.divisors, if d∣a then (ArithmeticFunction.moebius d:ℂ) else 0) =
      if a.Coprime h then 1 else 0 := by
  have hg : Nat.gcd h a≠0 := by
    intro hz
    exact hh (Nat.gcd_eq_zero_iff.mp hz).1
  have hd : (Nat.gcd h a).divisors = h.divisors.filter (fun d => d∣a) := by
    ext d
    simp only [Nat.mem_divisors,mem_filter,Nat.dvd_gcd_iff]
    tauto
  rw [← sum_filter,← hd,inducedGauss_mobius_indicator]
  simp only [Nat.coprime_comm]

/-- Scaling both the residue and modulus cancels exactly in the standard
additive character. The proof uses the actual exponential definition. -/
theorem inducedGauss_scaled_additive {d M : ℕ} [NeZero d] [NeZero M] (b : ℕ) :
    letI : NeZero (d*M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    ZMod.stdAddChar ((d*b:ℕ):ZMod (d*M)) = ZMod.stdAddChar (b:ZMod M) := by
  letI : NeZero (d*M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  have hleft := ZMod.stdAddChar_coe (N := d*M) ((d*b:ℕ):ℤ)
  have hright := ZMod.stdAddChar_coe (N := M) (b:ℤ)
  simp only [Int.cast_natCast] at hleft hright
  rw [hleft,hright]
  congr 1
  have hd : (d:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hm : (M:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  push_cast
  field_simp

end ZhangLS.Spec
