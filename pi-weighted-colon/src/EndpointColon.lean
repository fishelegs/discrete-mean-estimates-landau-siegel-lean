import DataIdealPresentation
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

noncomputable section

namespace PiWeightedColon

open Polynomial

abbrev F2 := ZMod 2
abbrev Plane := Bivariate F2

def endpoint (ε : Bool) : F2 := if ε then 1 else 0

def endpointD (ε : Bool) : ℕ := if ε then 3 else 1

def coordinate (ε : Bool) : Plane ≃+* Plane :=
  (algEquivAevalXAddC (X + C (endpoint ε))).toRingEquiv

theorem coordinate_C (ε : Bool) (p : Polynomial F2) : coordinate ε (C p) = C p := by
  simp [coordinate, algEquivAevalXAddC_apply]

theorem coordinate_X (ε : Bool) : coordinate ε X = X + C (X + C (endpoint ε)) := by
  simp [coordinate, algEquivAevalXAddC_apply]

def globalQ : Plane := (X ^ 2 + X + C X) ^ 2

theorem globalQ_expanded : globalQ = X ^ 4 + X ^ 2 + C (X ^ 2) := by
  simp only [globalQ, CharTwo.add_sq, ← pow_mul, C_pow]

theorem charTwo_local_identity {R : Type*} [CommRing R] [CharP R 2]
    (x y e : R) (he : e ^ 2 + e = 0) :
    ((x + y + e) ^ 2 + (x + y + e) + y) ^ 2 = x ^ 4 + x ^ 2 + y ^ 4 := by
  have hi : (x + y + e) ^ 2 + (x + y + e) + y = x ^ 2 + x + y ^ 2 := by
    calc
      _ = (x ^ 2 + x + y ^ 2) + (e ^ 2 + e) + (y + y) := by
        simp only [CharTwo.add_sq]
        ring
      _ = _ := by rw [he, CharTwo.add_self_eq_zero, add_zero, add_zero]
  rw [hi]
  simp only [CharTwo.add_sq, ← pow_mul]

theorem coordinate_globalQ (ε : Bool) : coordinate ε globalQ = localQ F2 := by
  have he : (C (C (endpoint ε)) : Plane) ^ 2 + C (C (endpoint ε)) = 0 := by
    cases ε <;> simp [endpoint, CharTwo.add_self_eq_zero]
  simp only [globalQ, map_pow, map_add, coordinate_X, coordinate_C]
  have hi := charTwo_local_identity (X : Plane) (C X) (C (C (endpoint ε))) he
  simpa only [localQ, C_pow, add_assoc] using hi

def endpointX (ε : Bool) : Plane := X + C X - C (C (endpoint ε))

def endpointJ (ε : Bool) : Ideal Plane :=
  Ideal.span {endpointX ε, C (X ^ endpointD ε)}

def endpointK (ε : Bool) : Ideal Plane :=
  Ideal.span {(endpointX ε) ^ 2, C (X ^ endpointD ε)}

theorem coordinate_endpointX (ε : Bool) : coordinate ε (endpointX ε) = X := by
  simp only [endpointX, map_sub, map_add, coordinate_X, coordinate_C]
  have h : (C X : Plane) + C X = 0 := CharTwo.add_self_eq_zero _
  calc
    _ = X + (C X + C X) := by ring
    _ = X := by rw [h, add_zero]

theorem coordinate_endpointJ (ε : Bool) :
    (endpointJ ε).map (coordinate ε) = localJ F2 (endpointD ε) := by
  rw [endpointJ, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, coordinate_endpointX, coordinate_C]
  congr 1
  simp [mono, ← C_mul_X_pow_eq_monomial]

theorem coordinate_endpointK (ε : Bool) :
    (endpointK ε).map (coordinate ε) = localK F2 (endpointD ε) := by
  rw [endpointK, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow, coordinate_endpointX, coordinate_C]
  congr 1
  simp [mono, ← C_mul_X_pow_eq_monomial]

theorem endpoint_membership (ε : Bool) (N : ℕ) (f : Plane) :
    f ∈ endpointJ ε * endpointK ε ^ N ↔
      coordinate ε f ∈ localJ F2 (endpointD ε) * localK F2 (endpointD ε) ^ N := by
  have hm : (endpointJ ε * endpointK ε ^ N).map (coordinate ε) =
      localJ F2 (endpointD ε) * localK F2 (endpointD ε) ^ N := by
    rw [Ideal.map_mul, Ideal.map_pow, coordinate_endpointJ, coordinate_endpointK]
  rw [← hm]
  exact Ideal.apply_mem_of_equiv_iff.symm

theorem endpoint_colon (ε : Bool) (N : ℕ) :
    (endpointJ ε * endpointK ε ^ (N + 1)).colon {globalQ} =
      endpointJ ε * endpointK ε ^ N := by
  ext f
  rw [Submodule.mem_colon_singleton, smul_eq_mul, endpoint_membership,
    map_mul, coordinate_globalQ]
  have hd : endpointD ε = 1 ∨ endpointD ε = 3 := by cases ε <;> simp [endpointD]
  have hlocal : coordinate ε f ∈ (localJ F2 (endpointD ε) *
      localK F2 (endpointD ε) ^ (N + 1)).colon {localQ F2} ↔
      coordinate ε f ∈ localJ F2 (endpointD ε) * localK F2 (endpointD ε) ^ N := by
    rw [localJK_colon hd N]
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hlocal
  exact hlocal.trans (endpoint_membership ε N f).symm

/-- The intersection `J₀ K₀^N ∩ J₁ K₁^N` from the proof target. -/
def dataIntersection (N : ℕ) : Ideal Plane :=
  (endpointJ false * endpointK false ^ N) ⊓ (endpointJ true * endpointK true ^ N)

/-- Weighted colon milestone for the actual endpoint-generated ideals. -/
theorem intersection_colon (N : ℕ) :
    (dataIntersection (N + 1)).colon {globalQ} = dataIntersection N := by
  rw [dataIntersection, Submodule.inf_colon, endpoint_colon, endpoint_colon]
  rfl

theorem intersection_colon_pred {N : ℕ} (hN : 1 ≤ N) :
    (dataIntersection N).colon {globalQ} = dataIntersection (N - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  simpa [Nat.add_comm] using intersection_colon n

end PiWeightedColon
