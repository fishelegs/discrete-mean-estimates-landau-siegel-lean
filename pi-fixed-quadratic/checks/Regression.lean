import FixedQuadratic.Envelope
import FixedQuadratic.MinorBudget
import FixedQuadratic.Comparison
import FixedQuadratic.Conjugation
import FixedQuadratic.Height
import FixedQuadratic.Weights
import FixedQuadratic.ParityDeterminant

open Polynomial
namespace FixedQuadratic.Regression

-- A nonmonic quadratic tests the exact a^d rather than an over-cleared a^(2d).
theorem nonmonic_resultant :
    ((C (2 : GaussianInt) * (X^2 - C 2)).resultant X 2 1 : ℂ) = -4 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h := quadratic_resultant_identity (C (2 : GaussianInt) * (X^2-C 2)) X 2
    (Real.sqrt 2) (-Real.sqrt 2) 1 (by simp) ?_
  · norm_num [GaussianInt.toComplex_def] at h
    calc
      _ = -(2 * (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) := h
      _ = -4 := by calc
        _ = -2 * (Real.sqrt 2 : ℂ)^2 := by ring
        _ = -4 := by rw [hs]; norm_num
  · norm_num [GaussianInt.toComplex_def, map_mul, map_sub, map_pow, map_X]
    ring_nf
    simp [← map_pow, hs]

/-- Actual false strengthening when the l1 cost is omitted. -/
theorem omitted_coefficient_cost_is_false :
    ¬ (1 ≤ |3 - 2*Real.sqrt 2| * Real.sqrt 2) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hlow : 1 < Real.sqrt 2 := by nlinarith
  have hhigh : Real.sqrt 2 < 3/2 := by nlinarith
  rw [abs_of_pos (by linarith : 0 < 3-2*Real.sqrt 2)]
  nlinarith

-- Max height and Mahler measure are distinct from the absolute Weil height.
theorem sqrt_two_mahler : quadraticMahler 1 (Real.sqrt 2) (-Real.sqrt 2) = 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have h : 1 ≤ Real.sqrt 2 := by nlinarith
  simp [quadraticMahler, abs_of_nonneg hp]

/-- An actual nonzero determinant can lose its highest coordinate powers. -/
theorem cancellation_minor :
    (Matrix.det (!![MvPolynomial.X (0 : Fin 1), MvPolynomial.X 0 + 1;
      MvPolynomial.X 0 - 1, MvPolynomial.X 0] :
        Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℚ))) = 1 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem cancellation_degree :
    (Matrix.det (!![MvPolynomial.X (0 : Fin 1), MvPolynomial.X 0 + 1;
      MvPolynomial.X 0 - 1, MvPolynomial.X 0] :
        Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℚ))).degreeOf 0 = 0 := by
  rw [cancellation_minor]
  simp

theorem bounded_height_two_finite : (boundedQuadraticRoots 2).Finite :=
  finite_boundedQuadraticRoots 2

theorem even_sqrt_two_norm :
    1 ≤ ‖((X^2+C 1 : Polynomial GaussianInt).map GaussianInt.toComplex).eval
      (Real.sqrt 2 : ℂ)‖ := by
  apply parity_eval_norm_one_le _ (Or.inl (by simp [add_comp, pow_comp])) (Real.sqrt 2) 2
    (Real.sq_sqrt (by norm_num))
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  · have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    norm_num [hs]

theorem odd_sqrt_two_norm :
    1 ≤ ‖((X : Polynomial GaussianInt).map GaussianInt.toComplex).eval (Real.sqrt 2 : ℂ)‖ := by
  apply parity_eval_norm_one_le _ (Or.inr (by simp)) (Real.sqrt 2) 2
    (Real.sq_sqrt (by norm_num))
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  · simp only [Polynomial.map_X, eval_X]
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

theorem nonparity_eval_below_one :
    ‖((C 3 - C 2*X : Polynomial GaussianInt).map GaussianInt.toComplex).eval (Real.sqrt 2 : ℂ)‖ < 1 := by
  have hv : ((C 3 - C 2*X : Polynomial GaussianInt).map GaussianInt.toComplex).eval
      (Real.sqrt 2 : ℂ) = ((3-2*Real.sqrt 2 : ℝ) : ℂ) := by
    norm_num [GaussianInt.toComplex_def]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hl : 1 < Real.sqrt 2 := by nlinarith
  have hh : Real.sqrt 2 < 3/2 := by nlinarith
  rw [hv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

end FixedQuadratic.Regression
