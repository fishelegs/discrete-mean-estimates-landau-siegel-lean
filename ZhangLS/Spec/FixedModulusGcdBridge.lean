import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import ZhangLS.Spec.Proposition141CharacterExpansion

/-! Exact fixed-modulus gcd reindexing and additive-character reduction.
No squarefree hypothesis is used and the modulus-one cases are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex
open scoped Classical ComplexConjugate

abbrev fixedDGcdIndex (D : ℕ) : Type :=
  Σ d : {d : ℕ+ // (d : ℕ) ∣ D}, {l : ℕ+ // Nat.Coprime (l : ℕ) (D / (d.val : ℕ))}

def fixedDGcdLift {D : ℕ} (i : fixedDGcdIndex D) : ℕ+ := i.1.val * i.2.val

lemma fixedDGcd_lift_gcd {D : ℕ} (i : fixedDGcdIndex D) :
    Nat.gcd (fixedDGcdLift i : ℕ) D = (i.1.val : ℕ) := by
  rcases i with ⟨⟨d,hd⟩,⟨l,hl⟩⟩
  change Nat.gcd ((d:ℕ)*(l:ℕ)) D = (d:ℕ)
  conv_lhs => rhs; rw [← Nat.mul_div_cancel' hd]
  rw [Nat.gcd_mul_left, hl.gcd_eq_one, mul_one]

theorem fixedDGcd_lift_injective (D : ℕ) : Function.Injective (@fixedDGcdLift D) := by
  intro x y he
  have hd : x.1 = y.1 := by
    apply Subtype.ext
    apply PNat.eq
    rw [← fixedDGcd_lift_gcd x, ← fixedDGcd_lift_gcd y, he]
  rcases x with ⟨d,⟨l,hl⟩⟩
  rcases y with ⟨e,⟨m,hm⟩⟩
  change d = e at hd
  subst e
  change d.val*l = d.val*m at he
  have hlm : l = m := mul_left_cancel he
  subst m
  rfl

theorem fixedDGcd_lift_surjective (D : ℕ) : Function.Surjective (@fixedDGcdLift D) := by
  intro l
  let g := Nat.gcd (l:ℕ) D
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ l.property
  have hgL : g ∣ (l:ℕ) := Nat.gcd_dvd_left _ _
  have hgD : g ∣ D := Nat.gcd_dvd_right _ _
  let d : ℕ+ := ⟨g,hg⟩
  let l1 : ℕ+ := ⟨(l:ℕ)/g, Nat.div_pos (Nat.le_of_dvd l.property hgL) hg⟩
  have hc : Nat.Coprime (l1:ℕ) (D/(d:ℕ)) :=
    Nat.gcd_div_gcd_div_gcd_of_pos_left l.property
  refine ⟨⟨⟨d,hgD⟩,⟨l1,hc⟩⟩,?_⟩
  apply PNat.eq
  exact Nat.mul_div_cancel' hgL

noncomputable def fixedDGcdEquiv (D : ℕ) : fixedDGcdIndex D ≃ ℕ+ :=
  Equiv.ofBijective fixedDGcdLift ⟨fixedDGcd_lift_injective D, fixedDGcd_lift_surjective D⟩

/-- The additional coprimality restriction is preserved exactly. -/
theorem fixedDGcd_coprime_iff {D : ℕ} (i : fixedDGcdIndex D) (k : ℕ) :
    Nat.Coprime (fixedDGcdLift i : ℕ) k ↔
      Nat.Coprime (i.1.val : ℕ) k ∧ Nat.Coprime (i.2.val : ℕ) k := by
  exact Nat.coprime_mul_iff_left

theorem fixedDGcd_quotient_pos {D : ℕ} (hD : 0 < D) (i : fixedDGcdIndex D) :
    0 < D/(i.1.val:ℕ) :=
  Nat.div_pos (Nat.le_of_dvd hD i.1.property) i.1.val.property

/-- The global positive-index equality does not require a convergence assertion. -/
theorem fixedDGcd_tsum_reindex {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (D : ℕ) (F : ℕ+ → A) :
    (∑' l : ℕ+, F l) = ∑' i : fixedDGcdIndex D, F (fixedDGcdLift i) :=
  ((fixedDGcdEquiv D).tsum_eq F).symm

theorem fixedDGcd_coprime_tsum_reindex {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (D k : ℕ) (F : ℕ+ → A) :
    (∑' l : ℕ+, if Nat.Coprime (l:ℕ) k then F l else 0) =
      ∑' i : fixedDGcdIndex D,
        if Nat.Coprime (i.1.val:ℕ) k ∧ Nat.Coprime (i.2.val:ℕ) k
        then F (fixedDGcdLift i) else 0 := by
  rw [fixedDGcd_tsum_reindex D]
  apply tsum_congr
  intro i
  simp only [fixedDGcd_coprime_iff]

/-- Summability is required before replacing the sigma sum by nested sums. -/
theorem fixedDGcd_nested_tsum {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (D : ℕ) (F : ℕ+ → A) (hF : Summable F) :
    (∑' l : ℕ+, F l) =
      ∑' d : {d : ℕ+ // (d:ℕ) ∣ D},
        ∑' l : {l : ℕ+ // Nat.Coprime (l:ℕ) (D/(d.val:ℕ))}, F (d.val*l.val) := by
  have hI : Summable (fun i : fixedDGcdIndex D => F (fixedDGcdLift i)) :=
    ((fixedDGcdEquiv D).summable_iff).mpr hF
  exact (fixedDGcd_tsum_reindex D F).trans hI.tsum_sigma

/-- Reduction of a genuine residue inverse through a divisor map. It is
proved by the unit equation rather than assuming compatibility of inverses. -/
theorem fixedDGcd_cast_inverse {M N p : ℕ} (hMN : M ∣ N)
    (hp : Nat.Coprime p N) :
    ZMod.castHom hMN (ZMod M) ((p:ZMod N)⁻¹) = (p:ZMod M)⁻¹ := by
  have hu : IsUnit (p:ZMod N) := (ZMod.isUnit_iff_coprime p N).mpr hp
  have he := congrArg (ZMod.castHom hMN (ZMod M)) (ZMod.mul_inv_of_unit _ hu)
  rw [map_mul, map_natCast, map_one] at he
  exact (ZMod.inv_eq_of_mul_eq_one M _ _ he).symm

/-- Scaling the numerator and modulus by the same positive integer is
exactly the quotient-map identity for standard additive characters. -/
theorem fixedDGcd_additive_quotient {d M : ℕ} [NeZero d] [NeZero M]
    (a : ZMod (d*M)) :
    letI : NeZero (d*M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    ZMod.stdAddChar ((d:ZMod (d*M))*a) =
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_left M d) (ZMod M) a) := by
  letI : NeZero (d*M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  have hn : a = (a.val:ZMod (d*M)) := (ZMod.natCast_zmod_val a).symm
  conv_lhs => rw [hn]
  conv_rhs => rw [hn]
  rw [map_natCast, ← Nat.cast_mul]
  have hleft := ZMod.stdAddChar_coe (N := d*M) ((d*a.val:ℕ):ℤ)
  have hright := ZMod.stdAddChar_coe (N := M) (a.val:ℤ)
  simp only [Int.cast_natCast] at hleft hright
  rw [hleft, hright]
  congr 1
  have hd : (d:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  push_cast
  field_simp

/-- Genuine inverse phases descend to the quotient modulus, for every
positive d,M, including d=1 and M=1. -/
theorem fixedDGcd_inverse_phase_quotient {d M p : ℕ} [NeZero d] [NeZero M]
    (hp : Nat.Coprime p (d*M)) (l : ℕ) :
    letI : NeZero (d*M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    ZMod.stdAddChar (-((d*l:ℕ):ZMod (d*M))*(p:ZMod (d*M))⁻¹) =
      ZMod.stdAddChar (-(l:ZMod M)*(p:ZMod M)⁻¹) := by
  letI : NeZero (d*M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  have hm : M ∣ d*M := Nat.dvd_mul_left M d
  calc
    _ = ZMod.stdAddChar ((d:ZMod (d*M))*(-(l:ZMod (d*M))*(p:ZMod (d*M))⁻¹)) := by
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [fixedDGcd_additive_quotient, map_mul, map_neg, map_natCast,
        fixedDGcd_cast_inverse hm hp]

end ZhangLS.Spec
