import HermiteComplexSpecialization
import HermiteRegression

noncomputable section

namespace PiWeightedColon.Regression

open Polynomial

theorem complex_actual_entry_at_I :
    aeval Complex.I (hermiteCoefficientEntry 1 1 1 2 1) = Complex.I + 2 := by
  rw [hermite_entry_nonconstant]
  simp

theorem complex_actual_matrix_entry_at_I :
    complexHermiteCoefficientMatrix 0 Complex.I (rationalSmallRowMap 3)
      (originalIndexEquiv 0 (rationalSmallColMap 3)) = Complex.I + 2 := by
  change aeval Complex.I (hermiteCoefficientMatrix 0 (rationalSmallRowMap 3)
    (originalIndexEquiv 0 (rationalSmallColMap 3))) = _
  rw [actual_hermite_scale_zero_entry]
  simp

theorem complex_actual_det_at_zero :
    (squareComplexHermiteCoefficientMatrix 0 rationalScaleZeroOrdering 0).det = 2 := by
  rw [← complexHermiteCoefficientMatrix_det_aeval]
  have h := actual_hermite_scale_zero_det_eval
  rw [← coeff_zero_eq_eval_zero] at h
  rw [← coeff_zero_eq_aeval_zero']
  simpa only [map_ofNat] using congrArg (algebraMap ℚ ℂ) h

theorem imaginaryRealParameter_one : imaginaryRealParameter 1 = 2 * Complex.I := by
  simp [imaginaryRealParameter]

theorem imaginaryRealParameter_two_not_transcendental :
    ¬ Transcendental ℚ (imaginaryRealParameter 2) := by
  rw [imaginaryRealParameter_transcendental_iff]
  exact not_not_intro (isAlgebraic_nat (R := ℚ) 2)

theorem piHermiteParameter_exact : piHermiteParameter = 2 * (Real.pi : ℂ) * Complex.I := rfl

end PiWeightedColon.Regression
