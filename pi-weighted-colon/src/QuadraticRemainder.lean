import RemainderVanish
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

noncomputable section

namespace PiWeightedColon

open Polynomial

def quadW : Line := X ^ 2 * u ^ 2

def quadPolynomial : Polynomial Line := X ^ 2 - C quadW

theorem quadPolynomial_monic : quadPolynomial.Monic :=
  monic_X_pow_sub_C quadW (by decide)

theorem quadPolynomial_degree : quadPolynomial.natDegree = 2 := by
  unfold quadPolynomial
  exact natDegree_X_pow_sub_C

abbrev Quad := AdjoinRoot quadPolynomial

def quadC : Line →+* Quad := AdjoinRoot.of quadPolynomial

def quadY : Quad := AdjoinRoot.root quadPolynomial

def quadRep : Quad →ₗ[Line] Polynomial Line := AdjoinRoot.modByMonicHom quadPolynomial_monic

def quadA (q : Quad) : Line := (quadRep q).coeff 0

def quadB (q : Quad) : Line := (quadRep q).coeff 1

def quadMk (A B : Line) : Quad := quadC A + quadC B * quadY

theorem quadY_sq : quadY ^ 2 = quadC quadW := by
  have h := AdjoinRoot.eval₂_root quadPolynomial
  change eval₂ (AdjoinRoot.of quadPolynomial) (AdjoinRoot.root quadPolynomial)
    (X ^ 2 - C quadW) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem quadRep_mk (A B : Line) : quadRep (quadMk A B) = C A + C B * X := by
  have he : quadMk A B = AdjoinRoot.mk quadPolynomial (C A + C B * X) := by
    simp [quadMk, quadC, quadY, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rw [he, quadRep, AdjoinRoot.modByMonicHom_mk]
  apply (modByMonic_eq_self_iff quadPolynomial_monic).mpr
  have hd : (C A + C B * X).natDegree ≤ 1 := by
    simpa using (natDegree_add_le (C A) (C B * X)).trans
      (max_le (by simp) (by simpa using (natDegree_mul_le (p := C B) (q := (X : Polynomial Line)))))
  by_cases hz : C A + C B * X = 0
  · simp [hz, degree_eq_natDegree quadPolynomial_monic.ne_zero]
  · rw [degree_eq_natDegree hz, degree_eq_natDegree quadPolynomial_monic.ne_zero,
      quadPolynomial_degree]
    exact_mod_cast (show (C A + C B * X).natDegree < 2 by omega)

theorem quadA_mk (A B : Line) : quadA (quadMk A B) = A := by
  simp [quadA, quadRep_mk]

theorem quadB_mk (A B : Line) : quadB (quadMk A B) = B := by
  simp [quadB, quadRep_mk]

theorem quad_canonical (q : Quad) : q = quadMk (quadA q) (quadB q) := by
  have hd : (quadRep q).natDegree ≤ 1 := by
    induction q using AdjoinRoot.induction_on with
    | ih p =>
      rw [quadRep, AdjoinRoot.modByMonicHom_mk]
      have h := natDegree_modByMonic_lt p quadPolynomial_monic
        (by intro he; have hh := congrArg Polynomial.natDegree he; simp [quadPolynomial_degree] at hh)
      rw [quadPolynomial_degree] at h
      omega
  have he := eq_X_add_C_of_natDegree_le_one hd
  have hm := AdjoinRoot.mk_leftInverse quadPolynomial_monic q
  change AdjoinRoot.mk quadPolynomial (quadRep q) = q at hm
  rw [he] at hm
  simpa [quadMk, quadA, quadB, quadC, quadY, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
    add_comm] using hm.symm

theorem quadA_add (q r : Quad) : quadA (q + r) = quadA q + quadA r := by
  simp [quadA, map_add]

theorem quadB_add (q r : Quad) : quadB (q + r) = quadB q + quadB r := by
  simp [quadB, map_add]

theorem quadA_zero : quadA 0 = 0 := by simp [quadA]

theorem quadB_zero : quadB 0 = 0 := by simp [quadB]

theorem quadMk_mul (A B D E : Line) :
    quadMk A B * quadMk D E = quadMk (A * D + quadW * B * E) (A * E + B * D) := by
  calc
    _ = quadC (A * D) + quadC (B * E) * quadY ^ 2 +
        (quadC (A * E) + quadC (B * D)) * quadY := by
      simp only [quadMk, map_mul]
      ring
    _ = _ := by
      rw [quadY_sq]
      simp only [quadMk, map_add, map_mul]
      ring

theorem quadA_mul (q r : Quad) :
    quadA (q * r) = quadA q * quadA r + quadW * quadB q * quadB r := by
  conv_lhs => rw [quad_canonical q, quad_canonical r, quadMk_mul, quadA_mk]

theorem quadB_mul (q r : Quad) :
    quadB (q * r) = quadA q * quadB r + quadB q * quadA r := by
  conv_lhs => rw [quad_canonical q, quad_canonical r, quadMk_mul, quadB_mk]

def innerReduction : Polynomial F2 →+* Quad := eval₂RingHom (quadC.comp C) quadY

def reduction : Plane →+* Quad := eval₂RingHom innerReduction (quadC X)

theorem reduction_t : reduction X = quadC X := by simp [reduction]

theorem reduction_y : reduction (C X) = quadY := by simp [reduction, innerReduction]

theorem reduction_constant (a : F2) : reduction (C (C a)) = quadC (C a) := by
  simp [reduction, innerReduction]

def lineEmbedding : Line →+* Plane := mapRingHom C

theorem reduction_line (A : Line) : reduction (lineEmbedding A) = quadC A := by
  unfold reduction lineEmbedding
  change eval₂ innerReduction (quadC X) (Polynomial.map C A) = quadC A
  rw [eval₂_map]
  have hi : innerReduction.comp C = quadC.comp C := by ext a; simp [innerReduction]
  rw [hi, ← hom_eval₂]
  simp

def linearRemainder (A B : Line) : Plane := lineEmbedding A + C X * lineEmbedding B

theorem reduction_linear (A B : Line) : reduction (linearRemainder A B) = quadMk A B := by
  simp only [linearRemainder, map_add, map_mul, reduction_line, reduction_y, quadMk]
  rw [mul_comm]

theorem reduction_Q : reduction globalQ = 0 := by
  rw [globalQ_expanded]
  simp only [map_add, map_pow, reduction_t]
  rw [reduction_y, quadY_sq, ← map_pow, ← map_pow, ← map_add, ← map_add]
  have he : (X : Line) ^ 4 + X ^ 2 + quadW = 0 := by
    simp only [quadW, u, CharTwo.add_sq, one_pow, mul_add, mul_one, ← pow_add]
    rw [show (2 : ℕ) + 2 = 4 by decide]
    have h := CharTwo.add_self_eq_zero ((X : Line) ^ 4 + X ^ 2)
    simpa only [add_assoc] using h
  rw [he, map_zero]

theorem reduction_remainder_eq (f h : Plane) (A B : Line)
    (he : f = globalQ * h + linearRemainder A B) : reduction f = quadMk A B := by
  rw [he, map_add, map_mul, reduction_Q, zero_mul, zero_add, reduction_linear]

end PiWeightedColon
