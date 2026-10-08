import HermitePolynomialNonvanishing
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

namespace PiWeightedColon

open Polynomial Matrix

/-- Evaluation of the actual Q[x] coefficients in C, with the rational algebra map. -/
def hermiteComplexEval (x : ℂ) : HermiteParameter →+* ℂ := (aeval x).toRingHom

def complexHermiteCoefficientMatrix (N : ℕ) (x : ℂ) :
    Matrix (RowIndex N) (OriginLabel N) ℂ :=
  (hermiteCoefficientMatrix N).map (hermiteComplexEval x)

theorem complexHermiteCoefficientMatrix_entry (N : ℕ) (x : ℂ)
    (r : RowIndex N) (c : OriginLabel N) :
    complexHermiteCoefficientMatrix N x r c =
      aeval x (hermiteCoefficientEntry (hermiteRowMultiplicity N (rowS r))
        (rowS r) (rowA r) c.val.2 (c.val.1 : ℚ)) := rfl

def squareComplexHermiteCoefficientMatrix (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) (x : ℂ) : Matrix (RowIndex N) (RowIndex N) ℂ :=
  (complexHermiteCoefficientMatrix N x).submatrix id e

theorem squareComplexHermiteCoefficientMatrix_map (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) (x : ℂ) :
    (squareHermiteCoefficientMatrix N e).map (hermiteComplexEval x) =
      squareComplexHermiteCoefficientMatrix N e x := rfl

theorem complexHermiteCoefficientMatrix_det_aeval (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) (x : ℂ) :
    aeval x ((squareHermiteCoefficientMatrix N e).det) =
      (squareComplexHermiteCoefficientMatrix N e x).det := by
  change (hermiteComplexEval x) ((squareHermiteCoefficientMatrix N e).det) = _
  rw [RingHom.map_det]
  rfl

/-- A proved conditional theorem for every complex number transcendental over Q. -/
theorem hermite_determinant_aeval_ne_zero (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) (x : ℂ) (hx : Transcendental ℚ x) :
    aeval x ((squareHermiteCoefficientMatrix N e).det) ≠ 0 := by
  intro hz
  exact hermiteCoefficientMatrix_det_ne_zero N e ((transcendental_iff.mp hx) _ hz)

theorem complexHermiteCoefficientMatrix_det_ne_zero (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) (x : ℂ) (hx : Transcendental ℚ x) :
    (squareComplexHermiteCoefficientMatrix N e x).det ≠ 0 := by
  rw [← complexHermiteCoefficientMatrix_det_aeval]
  exact hermite_determinant_aeval_ne_zero N e x hx

def canonicalComplexHermiteCoefficientMatrix (N : ℕ) (x : ℂ) :
    Matrix (RowIndex N) (RowIndex N) ℂ :=
  squareComplexHermiteCoefficientMatrix N ((matrixIndexEquiv N).trans (originalIndexEquiv N)) x

theorem canonicalComplexHermiteCoefficientMatrix_det_ne_zero (N : ℕ)
    (x : ℂ) (hx : Transcendental ℚ x) :
    (canonicalComplexHermiteCoefficientMatrix N x).det ≠ 0 :=
  complexHermiteCoefficientMatrix_det_ne_zero N _ x hx

theorem complex_I_isAlgebraic : IsAlgebraic ℚ Complex.I := by
  refine ⟨(X ^ 2 + 1 : Polynomial ℚ), ?_, ?_⟩
  · intro hp
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 2) hp
    norm_num [Polynomial.coeff_one] at hc
  · simp [Complex.I_sq]

/-- Multiplication by a nonzero algebraic complex number preserves transcendence. -/
theorem complex_transcendental_mul_iff (a b : ℂ) (ha : IsAlgebraic ℚ a) (hne : a ≠ 0) :
    Transcendental ℚ (a * b) ↔ Transcendental ℚ b := by
  apply not_congr
  constructor
  · intro hab
    have h := ha.inv.mul hab
    simpa [← mul_assoc, hne] using h
  · exact ha.mul

/-- This is 2*r*i for a real r; the result below does not assume anything about pi. -/
def imaginaryRealParameter (r : ℝ) : ℂ := 2 * (r : ℂ) * Complex.I

theorem imaginaryRealParameter_transcendental_iff (r : ℝ) :
    Transcendental ℚ (imaginaryRealParameter r) ↔ Transcendental ℚ r := by
  have ha : IsAlgebraic ℚ ((2 : ℂ) * Complex.I) :=
    (isAlgebraic_nat (R := ℚ) 2).mul complex_I_isAlgebraic
  have hn : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hr : Transcendental ℚ (r : ℂ) ↔ Transcendental ℚ r :=
    transcendental_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ) Complex.ofReal_injective
  rw [imaginaryRealParameter, mul_right_comm]
  exact (complex_transcendental_mul_iff _ _ ha hn).trans hr

theorem complexHermiteCoefficientMatrix_det_ne_zero_imaginaryReal (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) (r : ℝ) (hr : Transcendental ℚ r) :
    (squareComplexHermiteCoefficientMatrix N e (imaginaryRealParameter r)).det ≠ 0 :=
  complexHermiteCoefficientMatrix_det_ne_zero N e _
    ((imaginaryRealParameter_transcendental_iff r).mpr hr)

/-- The requested pi parameter. The pinned library does not prove its transcendence. -/
def piHermiteParameter : ℂ := imaginaryRealParameter Real.pi

/-- Exact reduction of the missing pi specialization input to transcendence of real pi.
This equivalence supplies neither side as an unconditional proposition. -/
theorem piHermiteParameter_transcendental_iff :
    Transcendental ℚ piHermiteParameter ↔ Transcendental ℚ Real.pi :=
  imaginaryRealParameter_transcendental_iff Real.pi

end PiWeightedColon
