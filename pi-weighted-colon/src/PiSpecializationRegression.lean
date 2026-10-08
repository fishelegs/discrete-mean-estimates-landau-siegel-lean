import PiHermiteNonvanishing
import SpecializationRegression

noncomputable section

namespace PiWeightedColon.Regression

open Polynomial

theorem actual_pi_input_exact_type : Transcendental ℚ Real.pi := real_pi_transcendental

theorem actual_two_pi_I_transcendental :
    Transcendental ℚ (2 * (Real.pi : ℂ) * Complex.I) := piHermiteParameter_transcendental

theorem actual_pi_det_all_N_all_original_orderings :
    ∀ (N : ℕ) (e : RowIndex N ≃ OriginLabel N),
      (squareComplexHermiteCoefficientMatrix N e (2 * (Real.pi : ℂ) * Complex.I)).det ≠ 0 :=
  complexHermiteCoefficientMatrix_det_ne_zero_two_pi_I

theorem actual_pi_polynomial_eval_all_N_all_original_orderings :
    ∀ (N : ℕ) (e : RowIndex N ≃ OriginLabel N),
      aeval (2 * (Real.pi : ℂ) * Complex.I) ((squareHermiteCoefficientMatrix N e).det) ≠ 0 :=
  hermite_determinant_aeval_ne_zero_pi

theorem actual_pi_canonical_all_N :
    ∀ N : ℕ, (canonicalComplexHermiteCoefficientMatrix N
      (2 * (Real.pi : ℂ) * Complex.I)).det ≠ 0 :=
  canonicalComplexHermiteCoefficientMatrix_det_ne_zero_pi

theorem actual_pi_scale_zero_det_ne_zero :
    (squareComplexHermiteCoefficientMatrix 0 rationalScaleZeroOrdering
      (2 * (Real.pi : ℂ) * Complex.I)).det ≠ 0 :=
  complexHermiteCoefficientMatrix_det_ne_zero_two_pi_I 0 rationalScaleZeroOrdering

theorem actual_pi_matrix_entry :
    complexHermiteCoefficientMatrix 0 piHermiteParameter (rationalSmallRowMap 3)
      (originalIndexEquiv 0 (rationalSmallColMap 3)) = piHermiteParameter + 2 := by
  change aeval piHermiteParameter (hermiteCoefficientMatrix 0 (rationalSmallRowMap 3)
    (originalIndexEquiv 0 (rationalSmallColMap 3))) = _
  rw [actual_hermite_scale_zero_entry]
  simp

end PiWeightedColon.Regression
