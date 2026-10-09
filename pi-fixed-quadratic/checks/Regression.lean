import FixedQuadratic.FixedFieldArithmetic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import FixedQuadratic.Selection
import FixedQuadratic.ErrorLimits
import Mathlib.NumberTheory.Real.Irrational
import FixedQuadratic.FormalEntry
import FixedQuadratic.LogClearing
import FixedQuadratic.MinorEnvelope
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

theorem actual_log_three :
    truncatedLog 3 = Polynomial.X - Polynomial.C (1/2 : ℂ)*Polynomial.X^2 := by
  ext n
  rw [truncatedLog, PowerSeries.coeff_trunc]
  by_cases hn : n < 3
  · rw [ite_eq_left hn, PowerSeries.coeff_log]
    interval_cases n <;> norm_num [Polynomial.coeff_sub, Polynomial.coeff_X,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  · rw [ite_eq_right hn]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, show 1 ≠ n by omega, show n ≠ 2 by omega]

theorem actual_log_entry_cleared :
    MvPolynomial.C (2 : ℂ) *
      formalEntry (fun _ : Fin 1 => 2*Complex.I) (fun _ => truncatedLog 3)
        2 0 (fun _ => 0) (fun _ => 1) = MvPolynomial.C (-1) := by
  rw [actual_log_three, formalEntry_split]
  simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X]
  rw [← map_mul]
  norm_num

theorem empty_log_denominator : logDenominator 0 = 1 ∧ logDenominator 1 = 1 := by
  norm_num [logDenominator, Nat.lcmUpto]

theorem actual_log_entry_integral :
    MvPolynomial.C (2 : ℂ) *
      formalEntry (fun _ : Fin 1 => 2*Complex.I) (fun _ => truncatedLog 3)
        2 0 (fun _ => 0) (fun _ => 1) ∈
      (MvPolynomial.map GaussianInt.toComplex :
        MvPolynomial (Fin 1) GaussianInt →+* MvPolynomial (Fin 1) ℂ).range := by
  have h := formalEntry_truncatedLog_cleared_gaussian
    (fun _ : Fin 1 => 3) 1 2 0 (fun _ => 0) (fun _ => 1)
  norm_num [logDenominator, Nat.lcmUpto, Finset.lcm_insert] at h
  exact h

theorem long_truncation_uniform :
    timeCoefficientL1 ((truncatedLog 100).map (MvPolynomial.C : ℂ →+*
      MvPolynomial (Fin 2) ℂ)) (1/2) ≤ 2 := truncatedLog_time_l1_le_two 100

theorem actual_log_entry_l1 :
    multiCoefficientL1 (MvPolynomial.C (2 : ℂ) *
      formalEntry (fun _ : Fin 1 => 2*Complex.I) (fun _ => truncatedLog 3)
        2 0 (fun _ => 0) (fun _ => 1)) = 1 := by
  rw [actual_log_entry_cleared, multiCoefficientL1_C]
  simp

theorem actual_empty_log_entry_envelope :
    multiCoefficientL1 (formalEntry (fun _ : Fin 1 => 2*Complex.I)
      (fun _ => truncatedLog 1) 0 0 (fun _ => 0) (fun _ => 2)) ≤ 64 := by
  have hh := formalEntry_truncatedLog_l1_coarse (fun _ : Fin 1 => 1)
    1 1 0 0 (fun _ => 0) (fun _ => 2) le_rfl
  norm_num at hh
  exact hh

theorem sqrt_two_degree_two : (minpoly ℚ (Real.sqrt 2)).natDegree = 2 := by
  have hp : Polynomial.aeval (Real.sqrt 2) (X^2-C 2 : Polynomial ℚ) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    norm_num [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have hi : IsIntegral ℚ (Real.sqrt 2) :=
    ⟨X^2-C 2, monic_X_pow_sub_C (2 : ℚ) (by norm_num : 2 ≠ 0), hp⟩
  have hlow := (minpoly.two_le_natDegree_iff hi).mpr irrational_sqrt_two
  have hdiv := minpoly.dvd ℚ (Real.sqrt 2) hp
  have hnonzero : (X^2-C 2 : Polynomial ℚ) ≠ 0 := by
    exact (monic_X_pow_sub_C (2 : ℚ) (by norm_num : 2 ≠ 0)).ne_zero
  have hupper := Polynomial.natDegree_le_of_dvd hdiv hnonzero
  norm_num [natDegree_X_pow_sub_C] at hupper
  omega

theorem sqrt_two_actual_primitive_data :
    (primitiveMinpoly (Real.sqrt 2)).IsPrimitive ∧
    Irreducible (primitiveMinpoly (Real.sqrt 2)) ∧
    0 < (primitiveMinpoly (Real.sqrt 2)).coeff 2 ∧
    Int.gcd (Int.gcd ((primitiveMinpoly (Real.sqrt 2)).coeff 2)
      ((primitiveMinpoly (Real.sqrt 2)).coeff 1) : ℤ)
      ((primitiveMinpoly (Real.sqrt 2)).coeff 0) = 1 :=
  ⟨primitiveMinpoly_primitive _, primitiveMinpoly_irreducible _ sqrt_two_degree_two,
    primitiveMinpoly_coeff_two_pos _ sqrt_two_degree_two,
    primitiveMinpoly_three_gcd _ sqrt_two_degree_two⟩

theorem sqrt_two_actual_height_mahler :
    Real.log (quadraticMahler ((primitiveMinpoly (Real.sqrt 2)).coeff 2 : ℝ)
      (Real.sqrt 2) (primitiveConjugate (Real.sqrt 2))) ≤
      (Nat.ceil (Real.log (primitiveMinpolyHeight (Real.sqrt 2) : ℝ)) : ℝ)+
      Real.log (Real.sqrt 3) :=
  primitiveMinpoly_mahler_log_le _ sqrt_two_degree_two

theorem actual_height_two_finite :
    {x : ℝ | (minpoly ℚ x).natDegree = 2 ∧ primitiveMinpolyHeight x ≤ 2}.Finite := by
  apply (finite_boundedQuadraticRoots 2).subset
  intro x hx
  exact primitiveMinpolyHeight_box x hx.1 2 hx.2

theorem actual_coefficient_envelope_36 :
    minorCoefficientEnvelope (ι := Fin 1) 1 (fun _ => 1) (fun _ => 2)
      (fun _ _ => 1) (fun _ _ => 0 : Fin 1 → Fin 1 → ℕ) = 36 := by
  norm_num [minorCoefficientEnvelope, minorDegrees]

theorem polynomial_row_factorial_vanishes : Filter.Tendsto
    (fun N : ℕ => Real.log ((N^2).factorial : ℝ)/((N^2 : ℕ)*N : ℝ))
    Filter.atTop (nhds 0) := by
  apply factorial_remainder_tendsto (fun N => N^2) 1 2 (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  constructor
  · positivity
  · simp

theorem actual_gaussian_fraction_field : IsFractionRing GaussianInt GaussianField :=
  inferInstance

theorem actual_gaussian_degree_two : Module.finrank ℚ GaussianField = 2 := gaussianField_finrank

/-- Constructs the actual real field Q(sqrt(2)), then checks relative degree
and Galois structure over the actual Gaussian fraction field. -/
theorem sqrt_two_actual_complexification :
    let F := IntermediateField.adjoin ℚ {Real.sqrt 2}
    Module.finrank GaussianField (Complexification F) = 2 ∧
    IsGalois GaussianField (Complexification F) := by
  dsimp
  let F := IntermediateField.adjoin ℚ {Real.sqrt 2}
  have hi := integral_of_minpoly_degree_two (Real.sqrt 2) sqrt_two_degree_two
  letI : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional hi
  have hF : Module.finrank ℚ F = 2 :=
    (IntermediateField.adjoin.finrank hi).trans sqrt_two_degree_two
  exact ⟨complexification_relative_degree F hF, complexification_isGalois F hF⟩

/-- Repeated coordinates are evaluated in the genuine common field, rather
than four fake Cartesian root pairs. -/
theorem sqrt_two_actual_repeated_norm (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2)
    (β : F) (hβ : (β : ℝ) = Real.sqrt 2) :
    ∃ σ : F ≃ₐ[ℚ] F, σ ≠ 1 ∧
      complexificationToComplex F
        ((algebraMap F (Complexification F) β+algebraMap F (Complexification F) β)*
          complexificationConjugation F σ
            (algebraMap F (Complexification F) β+algebraMap F (Complexification F) β)) = -8 := by
  obtain ⟨σ, hσ⟩ := exists_real_quadratic_conjugation F hF
  have hd : (minpoly ℚ (β : ℝ)).natDegree = 2 := hβ ▸ sqrt_two_degree_two
  have hmove := real_quadratic_conjugation_moves F hF σ hσ β hd
  have hsF : β^2 = (2 : F) := by
    apply Subtype.ext
    change (β : ℝ)^2 = 2
    rw [hβ]
    exact Real.sq_sqrt (by norm_num)
  have hs := congrArg σ hsF
  simp only [map_pow, map_ofNat] at hs
  have hsR : (σ β : ℝ)^2 = 2 := by
    have hh := congrArg F.val hs
    simpa only [map_pow, map_ofNat, IntermediateField.coe_val] using hh
  have hne : (σ β : ℝ) ≠ Real.sqrt 2 := by
    intro hh
    apply hmove
    exact Subtype.ext (hh.trans hβ.symm)
  have hneg : (σ β : ℝ) = -Real.sqrt 2 := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp
      (hsR.trans (Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)).symm) with he | he
    · exact (hne he).elim
    · exact he
  have ht : complexificationConjugation F σ (algebraMap F (Complexification F) β) =
      algebraMap F (Complexification F) (σ β) := by
    ext <;> simp [complexificationConjugation]
  refine ⟨σ, hσ, ?_⟩
  rw [map_add, map_mul, map_add, ht, map_add, complexification_real_eval,
    complexification_real_eval, hβ, hneg]
  have hsC : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  push_cast
  calc
    _ = -4*(Real.sqrt 2 : ℂ)^2 := by ring
    _ = -8 := by rw [hsC]; norm_num

end FixedQuadratic.Regression
