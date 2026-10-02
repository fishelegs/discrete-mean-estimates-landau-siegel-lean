import ZhangLS.Spec.Lemma56GaussianContour

#print axioms ZhangLS.Spec.lemma56_actual_four_zero_order_log_bound
#print axioms ZhangLS.Spec.lemma56_actual_common_maximum_log_detection
#print axioms ZhangLS.Spec.lemma56_general_repulsion_degree_bounds
#print axioms ZhangLS.Spec.lemma56_general_repulsion_exponential_cost
#print axioms ZhangLS.Spec.lemma56_general_repulsion_exceptional_cost_bound
#print axioms ZhangLS.Spec.lemma56_general_repulsion_strict_budget
#print axioms ZhangLS.Spec.lemma56_actual_log_budget_zero_exclusion
#print axioms ZhangLS.Spec.lemma56_actual_jensen_log_high_budget
#print axioms ZhangLS.Spec.lemma56_high_repulsion_scale_bounds
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_high_zero_exclusion
#print axioms ZhangLS.Spec.lemma56_actual_zero_removed_logDeriv_near_center_bound
#print axioms ZhangLS.Spec.lemma56_actual_logDeriv_bound_of_local_zero_gap
#print axioms ZhangLS.Spec.lemma56_actual_logDeriv_bound_from_high_zero_exclusion
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_high_logDeriv_bound
#print axioms ZhangLS.Spec.lemma56_high_scale_strict_margin
#print axioms ZhangLS.Spec.lemma56_actual_jensen_log_margin_budget
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_margin_zero_exclusion

open ZhangLS.Spec

example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ)) →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ s : ℂ, 1 - 2 / ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) < s.re →
      |s.im| ≤ 2 * Real.exp ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) →
        DirichletCharacter.LFunction θ s ≠ 0 :=
  lemma56_uniform_primitive_high_zero_exclusion

example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ σ : ℝ, 1 - 2 / ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) < σ →
      DirichletCharacter.LFunction θ
        ((σ : ℂ) + (2 * Real.exp ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) : ℂ) * Complex.I) ≠ 0 ∧
      DirichletCharacter.LFunction θ
        ((σ : ℂ) - (2 * Real.exp ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨D₀, hD₀⟩ := lemma56_uniform_primitive_high_zero_exclusion
  refine ⟨D₀, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq hqT hne σ hre
  have hf := hD₀ χ θ hDN hD hA hθ hq hqT hne
  constructor
  · apply hf
    · simpa using hre
    · simp [lemma23PaperL, Complex.exp_re, abs_of_pos (Real.exp_pos ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)))]
  · apply hf
    · simpa using hre
    · simp [lemma23PaperL, Complex.exp_re, abs_of_pos (Real.exp_pos ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)))]

example : ∃ D₀ : ℕ, ∀ {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ D), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → (D : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod D)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ s : ℂ, 1 - 2 / ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) < s.re →
      |s.im| ≤ 2 * Real.exp ((Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) →
        DirichletCharacter.LFunction θ s ≠ 0 := by
  obtain ⟨D₀, hD₀⟩ := lemma56_uniform_primitive_high_zero_exclusion
  exact ⟨D₀, fun χ θ hDN hD hA hθ hDT hne => hD₀ χ θ hDN hD hA hθ hD hDT hne⟩

#print axioms ZhangLS.Spec.lemma56_actual_logDeriv_bound_from_rectangular_zero_exclusion
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_margin_logDeriv_bound

example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ)) →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ z : ℂ, 1 - 1 / ((3 / 4 : ℝ) * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ Real.exp (2 * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) →
        ‖deriv (DirichletCharacter.LFunction θ) z / DirichletCharacter.LFunction θ z‖ ≤
          24 * ((3 / 4 : ℝ) * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) ^ 2 +
            28800 * ((3 / 4 : ℝ) * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) :=
  lemma56_uniform_primitive_margin_logDeriv_bound

-- The arithmetic series is the actual character times the von Mangoldt function.
-- No nonprincipal assumption is needed for the absolutely convergent line.
example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      -(deriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction θ ((2 : ℂ) + (t : ℂ) * Complex.I)) *
        ((x : ℂ) ^ ((2 : ℂ) + (t : ℂ) * Complex.I) *
          ((Real.sqrt Real.pi / B : ℝ) : ℂ) *
          Complex.exp (((2 : ℂ) + (t : ℂ) * Complex.I) ^ 2 / (4 * (B : ℂ) ^ 2))) =
      ∑' n : ℕ, θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Real.exp (-(B ^ 2 * (Real.log (x / (n : ℝ))) ^ 2)) : ℂ) := by
  simpa only [lemma56GaussianKernel, lemma56GaussianOmega,
    lemma56GaussianMangoldtSum, lemma56GaussianMangoldtTerm, lemma56GaussianWeight,
    lemma56Mangoldt, logDeriv, mul_assoc] using
      lemma56_actual_gaussian_mellin_identity θ hB hx

-- The modulus-one principal series is included in the exact Mellin identity.
example {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, -(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))
        ((2 : ℂ) + (t : ℂ) * Complex.I)) * lemma56GaussianKernel B 2 x t =
      lemma56GaussianMangoldtSum (1 : DirichletCharacter ℂ 1) B x :=
  lemma56_actual_gaussian_mellin_identity 1 hB hx

-- Integrability is proved independently of the identity, so the Bochner
-- integral is not using its default value on a nonintegrable function.
example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    MeasureTheory.Integrable (fun t : ℝ =>
      -(logDeriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * Complex.I)) *
        lemma56GaussianKernel B 2 x t) ∧
      Summable (fun n : ℕ => θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Real.exp (-(B ^ 2 * (Real.log (x / (n : ℝ))) ^ 2)) : ℂ)) := by
  refine ⟨lemma56_actual_gaussian_mellin_integrable θ hB hx, ?_⟩
  exact lemma56_actual_gaussian_mangoldt_summable θ hB hx

-- The scalar inverse Mellin line may have real part zero.
example {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    MeasureTheory.Integrable (lemma56GaussianKernel B 0 x) ∧
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56GaussianKernel B 0 x t =
        (Real.exp (-(B ^ 2 * (Real.log x) ^ 2)) : ℂ) :=
  ⟨lemma56_gaussian_kernel_integrable hB 0 hx,
    lemma56_gaussian_kernel_integral hB 0 hx⟩

example {B : ℝ} (hB : 0 < B) (σ : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56GaussianKernel B σ 1 t = 1 := by
  simpa only [lemma56_gaussian_weight_center, Complex.ofReal_one] using
    lemma56_gaussian_kernel_integral hB σ (x := 1) (by norm_num)

-- The natural zero index contributes zero, with no missing term in the tsum.
example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      lemma56GaussianMellinTerm θ B x 0 t = 0 := by
  simpa [lemma56GaussianMangoldtTerm, lemma56Mangoldt] using
    lemma56_gaussian_mellin_term_integral θ hB hx 0

-- All original assumptions precede the actual finite rectangle statement;
-- its vertical boundaries and the endpoints at +/- H are closed.
example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ)) →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {B x H : ℝ}, 0 < x → 0 ≤ H → H ≤ Real.exp (2 * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) →
      let a := 1 - 1 / ((3 / 4 : ℝ) * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ))
      Complex.I * (∫ t : ℝ in -H..H,
        lemma56GaussianArithmeticIntegrand θ B x ((2 : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.I * (∫ t : ℝ in -H..H,
          lemma56GaussianArithmeticIntegrand θ B x ((a : ℂ) + (t : ℂ) * Complex.I)) +
          (∫ σ : ℝ in a..2,
            lemma56GaussianArithmeticIntegrand θ B x ((σ : ℂ) + (H : ℂ) * Complex.I)) -
            (∫ σ : ℝ in a..2,
              lemma56GaussianArithmeticIntegrand θ B x ((σ : ℂ) - (H : ℂ) * Complex.I)) :=
  lemma56_uniform_primitive_gaussian_rectangle_shift

#print axioms ZhangLS.Spec.lemma56_gaussian_kernel_reciprocal
#print axioms ZhangLS.Spec.lemma56_gaussian_kernel_integrable
#print axioms ZhangLS.Spec.lemma56_gaussian_kernel_integral
#print axioms ZhangLS.Spec.lemma56_gaussian_weight_bounds
#print axioms ZhangLS.Spec.lemma56_gaussian_weight_center
#print axioms ZhangLS.Spec.lemma56_actual_mangoldt_summable_two
#print axioms ZhangLS.Spec.lemma56_gaussian_mellin_term_norm
#print axioms ZhangLS.Spec.lemma56_gaussian_mellin_term_integrable
#print axioms ZhangLS.Spec.lemma56_gaussian_mellin_integral_norm_summable
#print axioms ZhangLS.Spec.lemma56_gaussian_mellin_term_eq_kernel
#print axioms ZhangLS.Spec.lemma56_gaussian_mellin_term_integral
#print axioms ZhangLS.Spec.lemma56_actual_gaussian_mangoldt_summable
#print axioms ZhangLS.Spec.lemma56_gaussian_mellin_term_tsum
#print axioms ZhangLS.Spec.lemma56_actual_gaussian_mellin_integrable
#print axioms ZhangLS.Spec.lemma56_actual_gaussian_mellin_identity
#print axioms ZhangLS.Spec.lemma56_actual_gaussian_integrand_analyticAt
#print axioms ZhangLS.Spec.lemma56_actual_gaussian_rectangle_shift
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_gaussian_rectangle_shift
