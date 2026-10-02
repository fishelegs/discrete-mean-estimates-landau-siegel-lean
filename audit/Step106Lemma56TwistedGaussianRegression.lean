import ZhangLS.Spec.Lemma56PerronMarginBudget

open ZhangLS.Spec Complex
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

-- Actual oscillatory coefficients and actual L'/L, with no nonprincipal restriction.
example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      -(deriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I) /
        DirichletCharacter.LFunction θ ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) *
        lemma56GaussianKernel B 2 x t =
      ∑' n : ℕ, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
          (Real.exp (-(B ^ 2 * (Real.log (x / (n : ℝ))) ^ 2)) : ℂ) := by
  simpa only [lemma56TwistedGaussianMangoldtSum, lemma56TwistedGaussianMangoldtTerm,
    lemma56GaussianMangoldtTerm, lemma56Mangoldt, lemma56GaussianPhase,
    lemma56GaussianWeight, logDeriv, mul_assoc] using
      lemma56_actual_twisted_gaussian_mellin_identity θ hB hx τ

example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      -(logDeriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * I)) *
        lemma56GaussianKernel B 2 x t = lemma56GaussianMangoldtSum θ B x := by
  simpa [lemma56TwistedGaussianMangoldtSum, lemma56TwistedGaussianMangoldtTerm,
    lemma56GaussianPhase, lemma56GaussianMangoldtSum] using
      lemma56_actual_twisted_gaussian_mellin_identity θ hB hx 0

example {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    Summable (lemma56TwistedGaussianMangoldtTerm (1 : DirichletCharacter ℂ 1) B x τ) ∧
      MeasureTheory.Integrable (fun t : ℝ => -(logDeriv
        (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))
          ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56GaussianKernel B 2 x t) :=
  ⟨lemma56_actual_twisted_gaussian_mangoldt_summable 1 hB hx τ,
    lemma56_actual_twisted_gaussian_mellin_integrable 1 hB hx τ⟩

example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ)) →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {B H τ : ℝ}, 1 ≤ B → 0 ≤ H →
      H ≤ Real.exp (2 * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ)) / 2 → |τ| ≤ D →
      let a := 1 - 1 / ((3 / 4 : ℝ) * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ))
      (1 / (2 * Real.pi)) *
        ‖∫ t : ℝ in -H..H,
          lemma56TwistedGaussianArithmeticIntegrand θ B (Real.exp ((Real.log (D : ℝ)) ^ 9)) τ
            ((a : ℂ) + (t : ℂ) * I)‖ ≤
        (4150656 * Real.exp (1 / 4 : ℝ)) * Real.exp ((Real.log (D : ℝ)) ^ 9) *
          Real.exp (-((7 / 6 : ℝ) * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ))) :=
  lemma56_uniform_primitive_twisted_gaussian_paper_left_bound

-- Both oscillatory endpoints are included at the maximal allowed height.
example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {B : ℝ}, 1 ≤ B →
      let U := lemma23PaperL D ^ (9 / 2 : ℝ)
      let H := Real.exp (2 * U) / 2
      let a := 1 - 1 / ((3 / 4 : ℝ) * U)
      let rhs := (4150656 * Real.exp (1 / 4 : ℝ)) * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U))
      (1 / (2 * Real.pi)) * ‖∫ t : ℝ in -H..H,
        lemma56TwistedGaussianArithmeticIntegrand θ B (lemma23PaperP D) (D : ℝ)
          ((a : ℂ) + (t : ℂ) * I)‖ ≤ rhs ∧
      (1 / (2 * Real.pi)) * ‖∫ t : ℝ in -H..H,
        lemma56TwistedGaussianArithmeticIntegrand θ B (lemma23PaperP D) (-(D : ℝ))
          ((a : ℂ) + (t : ℂ) * I)‖ ≤ rhs := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_primitive_twisted_gaussian_paper_left_bound
  refine ⟨D₀, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B hB
  constructor
  · exact h χ θ hDN hD hA hθ hq1 hqT hne (B := B)
      (H := Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2) (τ := (D : ℝ))
      hB (by positivity) le_rfl (by simp)
  · exact h χ θ hDN hD hA hθ hq1 hqT hne (B := B)
      (H := Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2) (τ := -(D : ℝ))
      hB (by positivity) le_rfl (by simp)

example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (t τ : ℝ) :
    ‖deriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I) /
      DirichletCharacter.LFunction θ ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ ≤
        lemma56GaussianRightConstant :=
  lemma56_actual_logDeriv_two_uniform_bound θ (by simp)

-- The actual cumulative weight, independent summability, and principal inclusion.
example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      -(deriv (DirichletCharacter.LFunction θ) ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I) /
        DirichletCharacter.LFunction θ ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) *
          ((x : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) *
            Complex.exp (((2 : ℂ) + (t : ℂ) * I) ^ 2 / (4 * (B : ℂ) ^ 2)) /
              ((2 : ℂ) + (t : ℂ) * I)) =
      ∑' n : ℕ, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
          ((1 / 2 + (Real.sqrt Real.pi)⁻¹ *
            ∫ v : ℝ in (0 : ℝ)..B * Real.log (x / (n : ℝ)), Real.exp (-(v ^ 2)) : ℝ) : ℂ) := by
  simpa only [lemma56PerronKernel, lemma56PerronMangoldtSum, lemma56PerronMangoldtTerm,
    lemma56GaussianPhase, lemma56Mangoldt, lemma56PerronWeight] using
      lemma56_actual_perron_mellin_identity θ hB hx τ

example {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    Summable (lemma56PerronMangoldtTerm (1 : DirichletCharacter ℂ 1) B x τ) ∧
      MeasureTheory.Integrable (fun t : ℝ => -(logDeriv
        (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))
          ((2 : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56PerronKernel B 2 x t) :=
  ⟨lemma56_actual_perron_mangoldt_summable 1 hB hx τ,
    lemma56_actual_perron_mellin_integrable 1 hB hx τ⟩

example {B σ x : ℝ} (hB : 0 < B) (hσ : 0 < σ) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56PerronKernel B σ x t =
      ((1 / 2 + (Real.sqrt Real.pi)⁻¹ *
        ∫ v : ℝ in (0 : ℝ)..B * Real.log x, Real.exp (-(v ^ 2)) : ℝ) : ℂ) :=
  lemma56_perron_kernel_integral hB hσ hx

example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (B τ t : ℝ) :
    lemma56PerronMellinTerm θ B 1 τ 0 t = 0 := by
  simp [lemma56PerronMellinTerm]

example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x H : ℝ} (hB : 0 < B) (hx : 0 < x) (hH : 0 < H) (τ : ℝ) :
    ‖lemma56TwistedGaussianMangoldtSum θ B x τ -
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ in -H..H, lemma56TwistedGaussianArithmeticIntegrand θ B x τ
          ((2 : ℂ) + (t : ℂ) * I))‖ ≤
      (1 / (2 * Real.pi)) *
        (8 * lemma56GaussianRightConstant * x ^ 2 * Real.sqrt Real.pi * (B / H) *
          Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2))) :=
  lemma56_actual_twisted_gaussian_mangoldt_truncation θ hB hx hH τ

-- The logarithmic contour cost remains finite even at H = 0.
example : (∫ t : ℝ in -(0 : ℝ)..0, 1 / (1 + |t|)) = 0 := by simp

example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {B : ℝ}, 1 ≤ B →
      let U := lemma23PaperL D ^ (9 / 2 : ℝ)
      let H := Real.exp (2 * U) / 2
      let a := 1 - 1 / ((3 / 4 : ℝ) * U)
      let rhs := (2017218816 * Real.exp (1 / 4 : ℝ)) * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U))
      (1 / (2 * Real.pi)) * ‖∫ t : ℝ in -H..H,
        lemma56PerronArithmeticIntegrand θ B (lemma23PaperP D) (D : ℝ)
          ((a : ℂ) + (t : ℂ) * I)‖ ≤ rhs ∧
      (1 / (2 * Real.pi)) * ‖∫ t : ℝ in -H..H,
        lemma56PerronArithmeticIntegrand θ B (lemma23PaperP D) (-(D : ℝ))
          ((a : ℂ) + (t : ℂ) * I)‖ ≤ rhs := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_primitive_perron_paper_left_bound
  refine ⟨D₀, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B hB
  constructor
  · exact h χ θ hDN hD hA hθ hq1 hqT hne (B := B)
      (H := Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2) (τ := (D : ℝ))
      hB (by positivity) le_rfl (by simp)
  · exact h χ θ hDN hD hA hθ hq1 hqT hne (B := B)
      (H := Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2) (τ := -(D : ℝ))
      hB (by positivity) le_rfl (by simp)

example {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56PerronKernel B σ 1 t = (1 / 2 : ℂ) := by
  simpa [lemma56PerronWeight] using lemma56_perron_kernel_integral hB hσ (by norm_num : (0 : ℝ) < 1)

example : ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
    (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {B x : ℝ}, 0 < x →
      let H := Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2
      let a := 1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))
      I * (∫ t : ℝ in -H..H,
        lemma56PerronArithmeticIntegrand θ B x (D : ℝ) ((2 : ℂ) + (t : ℂ) * I)) =
        I * (∫ t : ℝ in -H..H,
          lemma56PerronArithmeticIntegrand θ B x (D : ℝ) ((a : ℂ) + (t : ℂ) * I)) +
          (∫ σ : ℝ in a..2,
            lemma56PerronArithmeticIntegrand θ B x (D : ℝ) ((σ : ℂ) + (H : ℂ) * I)) -
            (∫ σ : ℝ in a..2,
              lemma56PerronArithmeticIntegrand θ B x (D : ℝ) ((σ : ℂ) - (H : ℂ) * I)) := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_primitive_perron_rectangle_shift
  refine ⟨D₀, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B x hx
  exact h χ θ hDN hD hA hθ hq1 hqT hne hx (by positivity) le_rfl (by simp)

#print axioms ZhangLS.Spec.lemma56_paper_power_margin_identity
#print axioms ZhangLS.Spec.lemma56_gaussian_margin_polynomial_absorption
#print axioms ZhangLS.Spec.lemma56_paper_left_gaussian_budget
#print axioms ZhangLS.Spec.lemma56_gaussian_omega_norm
#print axioms ZhangLS.Spec.lemma56_gaussian_kernel_norm
#print axioms ZhangLS.Spec.lemma56_gaussian_kernel_norm_integral
#print axioms ZhangLS.Spec.lemma56_gaussian_phase_norm
#print axioms ZhangLS.Spec.lemma56_gaussian_phase_LSeries_term
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_mellin_term_norm
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_mellin_term_integrable
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_mellin_integral_norm_summable
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_mellin_term_integral
#print axioms ZhangLS.Spec.lemma56_actual_logDeriv_two_uniform_bound
#print axioms ZhangLS.Spec.lemma56_gaussian_right_constant_nonneg
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_right_envelope
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_right_eq
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_right_integrable
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_right_truncation
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_mangoldt_truncation
#print axioms ZhangLS.Spec.lemma56_actual_perron_integrand_analyticAt
#print axioms ZhangLS.Spec.lemma56_actual_perron_rectangle_shift
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_perron_rectangle_shift
#print axioms ZhangLS.Spec.lemma56_perron_base_scale_pos
#print axioms ZhangLS.Spec.lemma56_perron_weight_rescale
#print axioms ZhangLS.Spec.lemma56_perron_kernel_rescale
#print axioms ZhangLS.Spec.lemma56_perron_kernel_integrable
#print axioms ZhangLS.Spec.lemma56_perron_kernel_integral
#print axioms ZhangLS.Spec.lemma56_perron_vertical_intervalIntegrable
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_perron_left_bound
#print axioms ZhangLS.Spec.lemma56_perron_height_log_budget
#print axioms ZhangLS.Spec.lemma56_perron_margin_polynomial_absorption
#print axioms ZhangLS.Spec.lemma56_paper_left_perron_budget
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_perron_paper_left_bound
#print axioms ZhangLS.Spec.lemma56_actual_perron_mangoldt_summable
#print axioms ZhangLS.Spec.lemma56_perron_mellin_term_tsum
#print axioms ZhangLS.Spec.lemma56_actual_perron_mellin_integrable
#print axioms ZhangLS.Spec.lemma56_actual_perron_mellin_identity
#print axioms ZhangLS.Spec.lemma56_perron_kernel_norm_two
#print axioms ZhangLS.Spec.lemma56_perron_mellin_term_norm
#print axioms ZhangLS.Spec.lemma56_perron_mellin_term_eq_kernel
#print axioms ZhangLS.Spec.lemma56_perron_mellin_term_integrable
#print axioms ZhangLS.Spec.lemma56_perron_mellin_term_integral
#print axioms ZhangLS.Spec.lemma56_perron_mellin_integral_norm_summable
#print axioms ZhangLS.Spec.lemma56_perron_kernel_norm
#print axioms ZhangLS.Spec.lemma56_perron_kernel_log_majorant
#print axioms ZhangLS.Spec.lemma56_perron_log_majorant_integral
#print axioms ZhangLS.Spec.lemma56_perron_vertical_integral_bound
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_integrand_analyticAt
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_rectangle_shift
#print axioms ZhangLS.Spec.lemma56_margin_height_contains_modulus
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_twisted_gaussian_rectangle_shift
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_horizontal_point_bound
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_horizontal_integral_bound
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_twisted_gaussian_paper_left_bound
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_mangoldt_summable
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_mellin_term_tsum
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_mellin_integrable
#print axioms ZhangLS.Spec.lemma56_actual_twisted_gaussian_mellin_identity
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_vertical_intervalIntegrable
#print axioms ZhangLS.Spec.lemma56_twisted_gaussian_vertical_integral_bound
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_twisted_gaussian_left_bound
