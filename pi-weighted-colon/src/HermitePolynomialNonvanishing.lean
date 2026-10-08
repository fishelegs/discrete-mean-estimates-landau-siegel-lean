import RationalOriginNonvanishing
import Mathlib.Algebra.Polynomial.Div

noncomputable section

namespace PiWeightedColon

open Polynomial Matrix

abbrev HermiteParameter := Polynomial ℚ
abbrev HermiteBivariate := Polynomial HermiteParameter

def hermiteRowMultiplicity (N s : ℕ) : ℕ :=
  if s < 2 then N + 1 else N - (s - 2) / 4

theorem hermite_row_profile_iff (N s a : ℕ) :
    (a ≤ 2 * N + 1 ∧ s ≤ 4 * (N - a / 2) + 1) ↔
      (s ≤ 4 * N + 1 ∧ a < 2 * hermiteRowMultiplicity N s) := by
  unfold hermiteRowMultiplicity
  split <;> omega

theorem hermite_row_bounds {N : ℕ} (r : RowIndex N) :
    rowS r ≤ 4 * N + 1 ∧ rowA r < 2 * hermiteRowMultiplicity N (rowS r) :=
  (hermite_row_profile_iff N (rowS r) (rowA r)).mp (row_index_bounds r)

theorem hermite_row_multiplicity_pos {N : ℕ} (r : RowIndex N) :
    0 < hermiteRowMultiplicity N (rowS r) := by
  have h := (hermite_row_bounds r).2
  omega

/-- The outer variable is z and the inner variable is the actual parameter x. -/
def hermiteModulus (n : ℕ) : HermiteBivariate :=
  X ^ n * (X - C (X : HermiteParameter)) ^ n

theorem hermiteModulus_monic (n : ℕ) : (hermiteModulus n).Monic :=
  (monic_X.pow n).mul ((monic_X_sub_C _).pow n)

/-- The actual coefficient of the monic remainder of z^d modulo z^n(z-x)^n.
No closed-form binomial expression is assumed in this definition. -/
def hermiteRemainderCoefficient (n d a : ℕ) : HermiteParameter :=
  ((X ^ d : HermiteBivariate) %ₘ hermiteModulus n).coeff a

theorem hermiteModulus_map_zero (n : ℕ) :
    (hermiteModulus n).map (evalRingHom (0 : ℚ)) = (X ^ (2 * n) : Polynomial ℚ) := by
  simp [hermiteModulus, ← pow_add, two_mul]

theorem monomial_mod_X_power (d m : ℕ) :
    (X ^ d : Polynomial ℚ) %ₘ X ^ m = if d < m then X ^ d else 0 := by
  by_cases hd : d < m
  · rw [if_pos hd]
    apply (modByMonic_eq_self_iff (monic_X.pow m)).mpr
    simpa only [degree_X_pow] using (WithBot.coe_lt_coe.mpr hd)
  · rw [if_neg hd]
    apply (modByMonic_eq_zero_iff_dvd (monic_X.pow m)).mpr
    refine ⟨X ^ (d - m), ?_⟩
    rw [← pow_add]
    congr 1
    omega

theorem hermiteRemainderCoefficient_eval_zero (n d a : ℕ) :
    (hermiteRemainderCoefficient n d a).eval 0 = if d < 2 * n ∧ a = d then 1 else 0 := by
  change (evalRingHom (0 : ℚ)) (((X ^ d : HermiteBivariate) %ₘ hermiteModulus n).coeff a) = _
  rw [← coeff_map, map_modByMonic _ (hermiteModulus_monic n), hermiteModulus_map_zero]
  simp only [Polynomial.map_pow, Polynomial.map_X]
  rw [monomial_mod_X_power]
  by_cases hd : d < 2 * n <;> simp [hd, coeff_X_pow]

theorem hermiteRemainderCoefficient_eval_zero_of_row (n d a : ℕ) (ha : a < 2 * n) :
    (hermiteRemainderCoefficient n d a).eval 0 = if a = d then 1 else 0 := by
  rw [hermiteRemainderCoefficient_eval_zero]
  by_cases had : a = d
  · subst d
    simp [ha]
  · simp [had]

/-- The actual Hermite coefficient sum, as a polynomial in x. -/
def hermiteCoefficientEntry (n s a c : ℕ) (h : ℚ) : HermiteParameter :=
  ∑ ell ∈ Finset.range (min s c + 1),
    C ((c.choose ell : ℚ) * h ^ (s - ell) / ((s - ell).factorial : ℚ)) *
      hermiteRemainderCoefficient n (c - ell) a

theorem hermiteCoefficientEntry_eval_zero (n s a c : ℕ) (h : ℚ) (ha : a < 2 * n) :
    (hermiteCoefficientEntry n s a c h).eval 0 = rationalOriginEntry s a c h := by
  classical
  simp only [hermiteCoefficientEntry, eval_finsetSum, eval_mul, eval_C,
    hermiteRemainderCoefficient_eval_zero_of_row n _ a ha]
  by_cases hg : a ≤ c ∧ c ≤ s + a
  · have hi := (rational_origin_guard s a c).mp hg
    have hl : c - a ∈ Finset.range (min s c + 1) := by
      apply Finset.mem_range.mpr
      have hm : c - a ≤ min s c := Nat.le_min.mpr ⟨hi.2, Nat.sub_le _ _⟩
      omega
    rw [Finset.sum_eq_single (c - a)]
    · have he : a = c - (c - a) := by omega
      rw [if_pos he, mul_one, rationalOriginEntry, if_pos hg,
        Nat.choose_symm hg.1, rational_origin_exponent s a c hg.1 hg.2]
    · intro ell hell hne
      have hb := Finset.mem_range.mp hell
      have he : a ≠ c - ell := by
        have hc : ell ≤ c := by have h := Nat.min_le_right s c; omega
        intro he
        omega
      rw [if_neg he, mul_zero]
    · intro hn
      exact (hn hl).elim
  · rw [rationalOriginEntry, if_neg hg]
    apply Finset.sum_eq_zero
    intro ell hell
    have hb := Finset.mem_range.mp hell
    have he : a ≠ c - ell := by
      have hs : ell ≤ s := by have h := Nat.min_le_left s c; omega
      have hc : ell ≤ c := by have h := Nat.min_le_right s c; omega
      intro he
      apply hg
      omega
    rw [if_neg he, mul_zero]

def hermiteCoefficientMatrix (N : ℕ) : Matrix (RowIndex N) (OriginLabel N) HermiteParameter :=
  fun r c => hermiteCoefficientEntry (hermiteRowMultiplicity N (rowS r))
    (rowS r) (rowA r) c.val.2 (c.val.1 : ℚ)

theorem hermiteCoefficientMatrix_eval_zero (N : ℕ) :
    (hermiteCoefficientMatrix N).map (evalRingHom (0 : ℚ)) = rationalOriginMatrix N := by
  ext r c
  exact hermiteCoefficientEntry_eval_zero _ _ _ _ _ (hermite_row_bounds r).2

def squareHermiteCoefficientMatrix (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    Matrix (RowIndex N) (RowIndex N) HermiteParameter :=
  (hermiteCoefficientMatrix N).submatrix id e

theorem squareHermiteCoefficientMatrix_eval_zero (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (squareHermiteCoefficientMatrix N e).map (evalRingHom (0 : ℚ)) =
      squareRationalOriginMatrix N e := by
  ext r c
  exact hermiteCoefficientEntry_eval_zero _ _ _ _ _ (hermite_row_bounds r).2

theorem hermiteCoefficientMatrix_det_eval_zero (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    ((squareHermiteCoefficientMatrix N e).det).eval 0 = (squareRationalOriginMatrix N e).det := by
  change (evalRingHom (0 : ℚ)) ((squareHermiteCoefficientMatrix N e).det) = _
  rw [RingHom.map_det]
  exact congrArg Matrix.det (squareHermiteCoefficientMatrix_eval_zero N e)

theorem hermiteCoefficientMatrix_det_ne_zero (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (squareHermiteCoefficientMatrix N e).det ≠ 0 := by
  intro hz
  have h := hermiteCoefficientMatrix_det_eval_zero N e
  rw [hz, eval_zero] at h
  exact rationalOriginMatrix_det_ne_zero N e h.symm

def canonicalHermiteCoefficientMatrix (N : ℕ) : Matrix (RowIndex N) (RowIndex N) HermiteParameter :=
  squareHermiteCoefficientMatrix N ((matrixIndexEquiv N).trans (originalIndexEquiv N))

theorem canonicalHermiteCoefficientMatrix_det_ne_zero (N : ℕ) :
    (canonicalHermiteCoefficientMatrix N).det ≠ 0 := hermiteCoefficientMatrix_det_ne_zero N _

end PiWeightedColon
