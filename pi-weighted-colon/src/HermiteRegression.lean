import HermitePolynomialNonvanishing
import RationalRegression

noncomputable section

namespace PiWeightedColon.Regression

open Polynomial

/-- Exact division of z² by z(z-x), with quotient one and remainder xz. -/
theorem hermite_remainder_square :
    (X ^ 2 : HermiteBivariate) %ₘ hermiteModulus 1 = C (X : HermiteParameter) * X := by
  apply (div_modByMonic_unique 1 (C (X : HermiteParameter) * X)
    (hermiteModulus_monic 1) ⟨?_, ?_⟩).2
  · dsimp [hermiteModulus]
    ring
  · have hq : (hermiteModulus 1).degree = 2 := by
      norm_num [hermiteModulus, degree_X_sub_C]
    rw [hq, degree_C_mul_X (X_ne_zero : (X : HermiteParameter) ≠ 0)]
    decide

theorem hermite_remainder_linear :
    (X : HermiteBivariate) %ₘ hermiteModulus 1 = X := by
  apply (modByMonic_eq_self_iff (hermiteModulus_monic 1)).mpr
  norm_num [hermiteModulus, degree_X_sub_C]

theorem hermite_remainder_coefficients :
    hermiteRemainderCoefficient 1 2 1 = (X : HermiteParameter) ∧
    hermiteRemainderCoefficient 1 1 1 = 1 ∧
    hermiteRemainderCoefficient 1 2 0 = 0 := by
  simp [hermiteRemainderCoefficient, hermite_remainder_square, hermite_remainder_linear,
    coeff_X]

/-- This is the actual finite coefficient sum, and is nonconstant in x. -/
theorem hermite_entry_nonconstant :
    hermiteCoefficientEntry 1 1 1 2 1 = (X : HermiteParameter) + C 2 := by
  simp [hermiteCoefficientEntry, Finset.sum_range_succ,
    hermite_remainder_coefficients.1, hermite_remainder_coefficients.2.1, Nat.factorial]

theorem hermite_entry_parameter_coefficient :
    (hermiteCoefficientEntry 1 1 1 2 1).coeff 1 = 1 := by
  rw [hermite_entry_nonconstant]
  simp

theorem hermite_entry_eval_values :
    (hermiteCoefficientEntry 1 1 1 2 1).eval 0 = 2 ∧
    (hermiteCoefficientEntry 1 1 1 2 1).eval 1 = 3 := by
  rw [hermite_entry_nonconstant]
  norm_num

/-- The nonconstant entry is a genuine row and column of the N=0 matrix. -/
theorem actual_hermite_scale_zero_entry :
    hermiteCoefficientMatrix 0 (rationalSmallRowMap 3)
      (originalIndexEquiv 0 (rationalSmallColMap 3)) = (X : HermiteParameter) + C 2 := by
  change hermiteCoefficientEntry _ _ _ _ _ = _
  rw [originalIndexEquiv_coordinates]
  dsimp [rationalSmallRowMap, rationalSmallColMap, rowS, rowA,
    colE, colC, colK, natFrequency, parityBit, endpointD, hermiteRowMultiplicity]
  exact hermite_entry_nonconstant

theorem actual_hermite_scale_zero_det_eval :
    ((squareHermiteCoefficientMatrix 0 rationalScaleZeroOrdering).det).eval 0 = 2 := by
  rw [hermiteCoefficientMatrix_det_eval_zero, actual_rational_scale_zero_det]

theorem actual_hermite_scale_zero_det_ne_zero :
    (squareHermiteCoefficientMatrix 0 rationalScaleZeroOrdering).det ≠ 0 :=
  hermiteCoefficientMatrix_det_ne_zero 0 rationalScaleZeroOrdering

end PiWeightedColon.Regression
