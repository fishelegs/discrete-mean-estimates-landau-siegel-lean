import FixedQuadratic.FormalEntry
import FixedQuadratic.QuadraticNorm
import FixedQuadratic.FinitePlace
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

theorem primitive_three_coefficients :
    ∃ u v w : ℤ, u*6 + v*10 + w*15 = 1 :=
  primitive_quadratic_bezout 6 10 15 (by norm_num)

/-- The local root identity needs no monicity and works when a has positive valuation. -/
theorem nonmonic_local_root_identity (v : AbsoluteValue ℚ ℝ) (hv : IsNonarchimedean v) :
    v 2 * max 1 (v 1) * max 1 (v (1/2)) = 1 := by
  apply primitive_quadratic_root_identity v hv 2 (-3) 1 (by norm_num) 1 (1/2)
  have hf : C (2 : ℚ)*((X-C 1)*(X-C (1/2))) =
      C 2*X^2 + C (-2*(1+1/2 : ℚ))*X + C (2*1*(1/2 : ℚ)) := by
    simp only [map_neg, map_add, map_mul, map_one]; ring
  norm_num at hf ⊢
  exact hf.symm

/-- Repeated coordinates use the two compatible tuples, without mixed tuples. -/
theorem dependent_sqrt_two_local (v : AbsoluteValue ℂ ℝ) (hv : IsNonarchimedean v) :
    v (-8) ≤ 1 := by
  let P : MvPolynomial (Fin 2) GaussianInt := MvPolynomial.X 0 + MvPolynomial.X 1
  have he : ∀ i, P.degreeOf i ≤ 1 := by
    intro i
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    simp only [MvPolynomial.degreeOf_X, max_le_iff]
    constructor <;> split_ifs <;> norm_num
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hf : ∀ _ : Fin 2, C (1 : ℂ)*X^2 + C 0*X + C (-2) =
      C 1*((X-C (Real.sqrt 2 : ℂ))*(X-C (-Real.sqrt 2 : ℂ))) := by
    intro i
    have hfactor : C (1 : ℂ)*((X-C (Real.sqrt 2 : ℂ))*(X-C (-Real.sqrt 2 : ℂ))) =
        C 1*X^2 + C (-(1 : ℂ)*((Real.sqrt 2 : ℂ)+ -(Real.sqrt 2 : ℂ)))*X +
        C ((1 : ℂ)*(Real.sqrt 2 : ℂ)* -(Real.sqrt 2 : ℂ)) := by
      simp only [map_neg, map_add, map_mul, map_one]; ring
    simpa [← pow_two, hs] using hfactor.symm
  have h := cleared_product_nonarch_le_one v hv GaussianInt.toComplex P
    (fun _ => 1) (fun _ => 0) (fun _ => -2)
    (fun _ => (Real.sqrt 2 : ℂ)) (fun _ => (-Real.sqrt 2 : ℂ)) (fun _ => 1)
    he (by intro i; norm_num) (by intro i; simpa using hf i)
  simp [P, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X] at h
  have hp : ((Real.sqrt 2 : ℂ)+(Real.sqrt 2 : ℂ)) *
      (-(Real.sqrt 2 : ℂ)+ -(Real.sqrt 2 : ℂ)) = -8 := by
    calc
      _ = -4*(Real.sqrt 2 : ℂ)^2 := by ring
      _ = -8 := by rw [hs]; norm_num
  rw [← map_mul, hp] at h
  exact h

/-- Two repeated coordinates are cleared by a^2, rather than a^4, in the
same quadratic field. The relative-field hypothesis stays explicit. -/
theorem repeated_coordinate_gaussian {G K : Type*} [Field G] [Field K]
    [NumberField K] [Algebra GaussianInt G] [IsFractionRing GaussianInt G]
    [Algebra G K] [Algebra GaussianInt K] [IsScalarTower GaussianInt G K]
    [FiniteDimensional G K] [IsGalois G K]
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1)
    (a b c : ℤ) (β : K) (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1)
    (hf : C (a : K)*X^2+C (b : K)*X+C (c : K) =
      C (a : K)*((X-C β)*(X-C (τ β)))) :
    (a : K)^2*(β+β)*(τ β+τ β) ∈ (algebraMap GaussianInt K).range := by
  let P : MvPolynomial (Fin 2) GaussianInt := MvPolynomial.X 0+MvPolynomial.X 1
  have he : ∀ i, P.degreeOf i ≤ 1 := by
    intro i
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    simp only [MvPolynomial.degreeOf_X, max_le_iff]
    constructor <;> split_ifs <;> norm_num
  have h := quadratic_cleared_product_gaussian hdegree τ hτ P
    (fun _ => a) (fun _ => b) (fun _ => c) (fun _ => β) (fun _ => 1)
    he (fun _ => hprim) (fun _ => hf)
  simpa [P, Fin.prod_univ_two, pow_two] using h

theorem formal_entry_linear :
    formalEntry (fun _ : Fin 1 => 2*Complex.I) (fun _ => 0)
      0 0 (fun _ => 1) (fun _ => 2) =
        MvPolynomial.C (4*Complex.I) * MvPolynomial.X 0 := by
  rw [formalEntry_split]
  simp
  ring_nf
  norm_num [← map_pow]
  ring

theorem formal_entry_log_coefficient :
    formalEntry (fun _ : Fin 1 => 2*Complex.I)
      (fun _ => Polynomial.X - Polynomial.C (1/2 : ℂ)*Polynomial.X^2)
      2 0 (fun _ => 1) (fun _ => 2) = MvPolynomial.C (-1) := by
  rw [formalEntry_split]
  simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X]
  rw [← map_mul]
  norm_num

end FixedQuadratic.Regression
