import ZhangLS.Spec.InducedGaussFiniteSums
import Mathlib.Algebra.Group.Units.Equiv

/-! # Genuine CRT residue permutation for coprime Gauss products

The permutation sends (a,b) to n*a+m*b at modulus m*n. Multiplication by
n modulo m and by m modulo n is bijective because the moduli are coprime.
No character primitivity is needed for this residue identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def coprimeGaussResidueEquiv {m n : ℕ} (hmn : m.Coprime n) :
    ZMod m × ZMod n ≃ ZMod (m*n) :=
  ((ZMod.unitOfCoprime n hmn.symm).mulLeft.prodCongr
    (ZMod.unitOfCoprime m hmn).mulLeft).trans (ZMod.chineseRemainder hmn).symm.toEquiv

theorem coprimeGauss_residue_coordinates {m n : ℕ} (hmn : m.Coprime n)
    (a : ZMod m) (b : ZMod n) :
    ZMod.chineseRemainder hmn (coprimeGaussResidueEquiv hmn (a,b)) =
      ((n:ZMod m)*a,(m:ZMod n)*b) := by
  change ZMod.chineseRemainder hmn ((ZMod.chineseRemainder hmn).symm
    (((ZMod.unitOfCoprime n hmn.symm:ZMod m)*a),
      ((ZMod.unitOfCoprime m hmn:ZMod n)*b))) = _
  rw [RingEquiv.apply_symm_apply]
  simp only [ZMod.coe_unitOfCoprime]

/-- The representative is proved through the genuine CRT, not guessed
from a displayed inverse residue. -/
theorem coprimeGauss_residue_nat {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (a : ZMod m) (b : ZMod n) :
    coprimeGaussResidueEquiv hmn (a,b) = ((n*a.val+m*b.val:ℕ):ZMod (m*n)) := by
  apply (ZMod.chineseRemainder hmn).injective
  rw [coprimeGauss_residue_coordinates,map_natCast]
  apply Prod.ext
  · simp only [Prod.fst_add,Prod.fst_mul,Prod.fst_natCast,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,
      ZMod.natCast_self,zero_mul,add_zero]
  · simp only [Prod.snd_add,Prod.snd_mul,Prod.snd_natCast,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,
      ZMod.natCast_self,zero_mul,zero_add]

/-- Actual additive-character factorization on that permutation. -/
theorem coprimeGauss_additive_factorization {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (a : ZMod m) (b : ZMod n) :
    letI : NeZero (m*n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    ZMod.stdAddChar (coprimeGaussResidueEquiv hmn (a,b)) =
      ZMod.stdAddChar a*ZMod.stdAddChar b := by
  letI : NeZero (m*n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [coprimeGauss_residue_nat,Nat.cast_add,AddChar.map_add_eq_mul]
  have hnphase : ZMod.stdAddChar ((n*a.val:ℕ):ZMod (m*n))=ZMod.stdAddChar a := by
    have hleft := ZMod.stdAddChar_coe (N := m*n) ((n*a.val:ℕ):ℤ)
    have hright := ZMod.stdAddChar_coe (N := m) (a.val:ℤ)
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val] at hleft hright
    rw [hleft,hright]
    congr 1
    have hmC : (m:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
    have hnC : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    push_cast
    field_simp
  have hmphase : ZMod.stdAddChar ((m*b.val:ℕ):ZMod (m*n))=ZMod.stdAddChar b := by
    have hh := inducedGauss_scaled_additive (d := m) (M := n) b.val
    simpa only [ZMod.natCast_zmod_val] using hh
  rw [hnphase,hmphase]

end ZhangLS.Spec
