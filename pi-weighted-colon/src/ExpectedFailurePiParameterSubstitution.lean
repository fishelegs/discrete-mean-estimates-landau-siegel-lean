import PiHermiteNonvanishing

open PiWeightedColon

example (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (squareComplexHermiteCoefficientMatrix N e (4 * Complex.I)).det ≠ 0 := by
  exact complexHermiteCoefficientMatrix_det_ne_zero_pi N e
