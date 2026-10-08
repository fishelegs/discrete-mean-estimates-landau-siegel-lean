import HermiteComplexSpecialization
import LeanFormalizations.NumberTheory.Transcendence.PiTranscendental

noncomputable section

namespace PiWeightedColon

open Polynomial Matrix

/-- The separately attributed six-file A7 proof supplies the ordinary real pi input. -/
theorem real_pi_transcendental : Transcendental ℚ Real.pi :=
  LeanFormalizations.Transcendence.transcendental_pi_axiomClean

theorem piHermiteParameter_transcendental : Transcendental ℚ piHermiteParameter :=
  piHermiteParameter_transcendental_iff.mpr real_pi_transcendental

/-- Evaluation of the actual determinant polynomial at 2*pi*i, for every N and ordering. -/
theorem hermite_determinant_aeval_ne_zero_pi (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) :
    aeval piHermiteParameter ((squareHermiteCoefficientMatrix N e).det) ≠ 0 :=
  hermite_determinant_aeval_ne_zero N e _ piHermiteParameter_transcendental

/-- The actual complex Hermite matrix at pi; no transcendence hypothesis remains. -/
theorem complexHermiteCoefficientMatrix_det_ne_zero_pi (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) :
    (squareComplexHermiteCoefficientMatrix N e piHermiteParameter).det ≠ 0 :=
  complexHermiteCoefficientMatrix_det_ne_zero N e _ piHermiteParameter_transcendental

/-- The literal 2*pi*i parameter with every original-column reindexing. -/
theorem complexHermiteCoefficientMatrix_det_ne_zero_two_pi_I (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) :
    (squareComplexHermiteCoefficientMatrix N e (2 * (Real.pi : ℂ) * Complex.I)).det ≠ 0 :=
  complexHermiteCoefficientMatrix_det_ne_zero_pi N e

theorem canonicalComplexHermiteCoefficientMatrix_det_ne_zero_pi (N : ℕ) :
    (canonicalComplexHermiteCoefficientMatrix N piHermiteParameter).det ≠ 0 :=
  canonicalComplexHermiteCoefficientMatrix_det_ne_zero N _ piHermiteParameter_transcendental

end PiWeightedColon
