import ZhangLS.Spec.Lemma82

namespace ZhangLS.Spec
open Complex Finset
open scoped Real

/-- Exact original P endpoint. -/
theorem lemma82_regression_P (D : ℕ) :
    lemma23PaperP D = Real.exp (Real.log (D:ℝ)^9) := rfl

/-- Exact original T endpoint, with 1.1 represented without rounding. -/
theorem lemma82_regression_T (D : ℕ) :
    lemma56PaperT D = Real.exp (Real.log (D:ℝ)^(11/10:ℝ)) := rfl

theorem lemma82_regression_beta_one (D : ℕ) (c : ℝ) :
    lemma82PaperBeta D c 0 = lemma52PaperBetaOne D c := by
  simp [lemma82PaperBeta]

theorem lemma82_regression_beta_two (D : ℕ) (c : ℝ) :
    lemma82PaperBeta D c 1 = lemma52PaperBetaTwo D c := by
  simp [lemma82PaperBeta]

theorem lemma82_regression_beta_three (D : ℕ) (c : ℝ) :
    lemma82PaperBeta D c 2 = lemma52PaperBetaThree D c := by
  simp [lemma82PaperBeta]


/-- The c′ perturbations are the literal original (2.13) formulas. -/
theorem lemma82_regression_beta_formulas (D : ℕ) (c : ℝ) :
    lemma82PaperBeta D c 0 = I*((lemma44PaperAlpha D *
      (1-5*c*lemma44PaperAlpha D*lemma23PaperL D):ℝ):ℂ) ∧
    lemma82PaperBeta D c 1 = I*((2*lemma44PaperAlpha D *
      (1+c*lemma44PaperAlpha D*lemma23PaperL D):ℝ):ℂ) ∧
    lemma82PaperBeta D c 2 = I*((3*lemma44PaperAlpha D *
      (1-c*lemma44PaperAlpha D*lemma23PaperL D):ℝ):ℂ) := by
  simp [lemma82PaperBeta,lemma52PaperBetaOne,lemma52PaperBetaTwo,lemma52PaperBetaThree,
    lemma23PaperOffsetOne,lemma23PaperOffsetTwo,lemma23PaperOffsetThree]

theorem lemma82_regression_cyclic_wrap (D : ℕ) (c : ℝ) :
    lemma82PaperBeta D c ((2:Fin 3)+1) = lemma52PaperBetaOne D c ∧
    lemma82PaperBeta D c ((2:Fin 3)+2) = lemma52PaperBetaTwo D c := by
  rw [show ((2:Fin 3)+1)=0 by decide, show ((2:Fin 3)+2)=1 by decide]
  simp [lemma82PaperBeta]

theorem lemma82_regression_cyclic (D : ℕ) (c : ℝ) (j : Fin 3) :
    lemma82PaperBeta D c (j+3) = lemma82PaperBeta D c j := by simp

theorem lemma82_regression_beta_six (D : ℕ) :
    lemma82SmoothingBeta D 6 = 3*I*(lemma44PaperAlpha D:ℂ)/2 := by
  simp [lemma82SmoothingBeta]

theorem lemma82_regression_beta_seven (D : ℕ) :
    lemma82SmoothingBeta D 7 = 5*I*(lemma44PaperAlpha D:ℂ)/2 := by
  simp [lemma82SmoothingBeta]

/-- At an integer endpoint the strict cutoff excludes that integer. -/
theorem lemma82_regression_strict_endpoint (N : ℕ) :
    N ∉ lemma82StrictCutoff (N:ℝ) := by
  simp [lemma82StrictCutoff]

/-- The inclusive endpoint has zero original summand. -/
theorem lemma82_regression_endpoint_weight {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ N : ℕ) (hN : 0<N) :
    χ.evalNat N/(N:ℂ)^(1-lemma82PaperBeta D c j) *
      (((N:ℝ)/(N:ℝ):ℝ):ℂ)^(lemma82SmoothingBeta D μ) *
        (Real.log ((N:ℝ)/(N:ℝ)):ℂ) = 0 := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  simp [hn]

/-- Literal expansion of the proved target in original sums and powers. -/
theorem lemma82_original_expanded :
  ∃ C : ℝ, 0<C ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ x : ℝ,
        Real.exp (Real.log (D:ℝ)^(11/10:ℝ)) < x →
        x < Real.exp (Real.log (D:ℝ)^9) →
        ∀ j : Fin 3, ∀ μ : ℕ, (μ=6 ∨ μ=7) →
          ‖(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n:ℝ)<x),
              χ.evalNat n/(n:ℂ)^(1-lemma82PaperBeta D c j) *
                ((x/(n:ℝ):ℝ):ℂ)^(lemma82SmoothingBeta D μ) *
                  (Real.log (x/(n:ℝ)):ℂ)) -
            LDerivAtOne χ * ((1+(lemma82SmoothingBeta D μ-lemma82PaperBeta D c j)*
              (Real.log x : ℂ))*(x:ℂ)^(lemma82SmoothingBeta D μ))‖ ≤
            C*Real.log (D:ℝ)^(-6:ℤ) := by
  exact lemma82_original

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma82FinitePolynomial
#print axioms ZhangLS.Spec.lemma82_sum_zero_endpoint
#print axioms ZhangLS.Spec.lemma82_finite_abel
#print axioms ZhangLS.Spec.lemma82_abel_tail_norm
#print axioms ZhangLS.Spec.lemma82_actual_abel_remainder
#print axioms ZhangLS.Spec.lemma82ScaledRemainder
#print axioms ZhangLS.Spec.lemma82_scaled_remainder_norm
#print axioms ZhangLS.Spec.lemma82_finite_polynomial_differentiable
#print axioms ZhangLS.Spec.lemma82_scaled_remainder_differentiable
#print axioms ZhangLS.Spec.lemma82_scaled_remainder_deriv_norm
#print axioms ZhangLS.Spec.lemma82WeightedPolynomial
#print axioms ZhangLS.Spec.lemma82_scaled_polynomial_hasDerivAt
#print axioms ZhangLS.Spec.lemma82_scaled_remainder_deriv
#print axioms ZhangLS.Spec.lemma82_weighted_abel_error
#print axioms ZhangLS.Spec.lemma82_strict_weighted_eq
#print axioms ZhangLS.Spec.lemma82PaperBeta
#print axioms ZhangLS.Spec.lemma82SmoothingBeta
#print axioms ZhangLS.Spec.lemma82StrictCutoff
#print axioms ZhangLS.Spec.lemma82ShiftedSum
#print axioms ZhangLS.Spec.lemma82MainTerm
#print axioms ZhangLS.Spec.Lemma82Target
#print axioms ZhangLS.Spec.lemma82_beta_re
#print axioms ZhangLS.Spec.lemma82_smoothing_beta_re
#print axioms ZhangLS.Spec.lemma82_mem_strictCutoff
#print axioms ZhangLS.Spec.lemma82_positive_ratio_cpow
#print axioms ZhangLS.Spec.lemma82_original_term
#print axioms ZhangLS.Spec.lemma82_shifted_sum_eq_weighted
#print axioms ZhangLS.Spec.lemma82_original_analytic_bridge
#print axioms ZhangLS.Spec.lemma82LocalErrorConstant
#print axioms ZhangLS.Spec.lemma82_local_error_constant_pos
#print axioms ZhangLS.Spec.lemma82_beta_norm
#print axioms ZhangLS.Spec.lemma82_smoothing_beta_norm
#print axioms ZhangLS.Spec.lemma82_shift_in_disk
#print axioms ZhangLS.Spec.lemma82_local_analytic_error
#print axioms ZhangLS.Spec.lemma82_tail_absorption_eventually
#print axioms ZhangLS.Spec.lemma82_uniform_threshold
#print axioms ZhangLS.Spec.lemma82ErrorConstant
#print axioms ZhangLS.Spec.lemma82_error_constant_pos
#print axioms ZhangLS.Spec.lemma82_at_parameters
#print axioms ZhangLS.Spec.lemma82_original
#print axioms ZhangLS.Spec.lemma82_regression_P
#print axioms ZhangLS.Spec.lemma82_regression_T
#print axioms ZhangLS.Spec.lemma82_regression_beta_one
#print axioms ZhangLS.Spec.lemma82_regression_beta_two
#print axioms ZhangLS.Spec.lemma82_regression_beta_three
#print axioms ZhangLS.Spec.lemma82_regression_beta_formulas
#print axioms ZhangLS.Spec.lemma82_regression_cyclic_wrap
#print axioms ZhangLS.Spec.lemma82_regression_cyclic
#print axioms ZhangLS.Spec.lemma82_regression_beta_six
#print axioms ZhangLS.Spec.lemma82_regression_beta_seven
#print axioms ZhangLS.Spec.lemma82_regression_strict_endpoint
#print axioms ZhangLS.Spec.lemma82_regression_endpoint_weight
#print axioms ZhangLS.Spec.lemma82_original_expanded
