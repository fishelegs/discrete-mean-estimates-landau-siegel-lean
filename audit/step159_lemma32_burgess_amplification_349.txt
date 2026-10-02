import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace ZhangLS.Spec

def lemma32BurgessDeterminant (M : ℤ) (a b : ℕ) {N : ℕ} (n m : Fin N) : ℤ :=
  (a : ℤ)*(M+(m.val : ℤ))-(b : ℤ)*(M+(n.val : ℤ))

lemma lemma32_burgess_determinant_variation (M : ℤ) (a b : ℕ) {N : ℕ}
    (n m n' m' : Fin N) :
    (lemma32BurgessDeterminant M a b n m-
      lemma32BurgessDeterminant M a b n' m').natAbs ≤ (a+b)*N := by
  have he : lemma32BurgessDeterminant M a b n m-
      lemma32BurgessDeterminant M a b n' m' =
      (a : ℤ)*((m.val : ℤ)-(m'.val : ℤ))-(b : ℤ)*((n.val : ℤ)-(n'.val : ℤ)) := by
    unfold lemma32BurgessDeterminant
    ring
  rw [he]
  calc
    _ ≤ ((a : ℤ)*((m.val : ℤ)-(m'.val : ℤ))).natAbs+
        ((b : ℤ)*((n.val : ℤ)-(n'.val : ℤ))).natAbs := Int.natAbs_sub_le _ _
    _ = a*((m.val : ℤ)-(m'.val : ℤ)).natAbs+
        b*((n.val : ℤ)-(n'.val : ℤ)).natAbs := by rw [Int.natAbs_mul, Int.natAbs_mul];simp
    _ ≤ a*N+b*N := Nat.add_le_add
      (Nat.mul_le_mul_left a (Int.natAbs_coe_sub_coe_le_of_le m.isLt.le m'.isLt.le))
      (Nat.mul_le_mul_left b (Int.natAbs_coe_sub_coe_le_of_le n.isLt.le n'.isLt.le))
    _ = _ := by ring

lemma lemma32_burgess_determinant_unique {D A N a b : ℕ}
    (hsize : 2*A*N < D) (ha : a ≤ A) (hb : b ≤ A) (M : ℤ)
    (n m n' m' : Fin N)
    (h1 : (D : ℤ) ∣ lemma32BurgessDeterminant M a b n m)
    (h2 : (D : ℤ) ∣ lemma32BurgessDeterminant M a b n' m') :
    lemma32BurgessDeterminant M a b n m=lemma32BurgessDeterminant M a b n' m' := by
  apply Int.eq_of_sub_eq_zero
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_sub h1 h2)
  rw [Int.natAbs_natCast]
  calc
    _ ≤ (a+b)*N := lemma32_burgess_determinant_variation M a b n m n' m'
    _ ≤ (2*A)*N := Nat.mul_le_mul_right N (by omega)
    _ < D := hsize

end ZhangLS.Spec
