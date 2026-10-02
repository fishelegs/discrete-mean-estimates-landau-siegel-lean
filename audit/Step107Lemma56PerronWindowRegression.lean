import ZhangLS.Spec.Lemma56PerronNearError

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open ZhangLS.Spec Complex

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
    (q : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ)) →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {x τ : ℝ}, 1 ≤ x → x ≤ 2 * Real.exp ((Real.log (D : ℝ)) ^ 9) → |τ| ≤ D →
      let U := (Real.log (D : ℝ)) ^ (9 / 2 : ℝ)
      let B := Real.exp ((3 / 2 : ℝ) * U)
      ‖∑' n : ℕ, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
          ((1 / 2 + (Real.sqrt Real.pi)⁻¹ *
            ∫ v : ℝ in (0 : ℝ)..B * Real.log (x / (n : ℝ)), Real.exp (-(v ^ 2)) : ℝ) : ℂ)‖ ≤
        C * Real.exp ((Real.log (D : ℝ)) ^ 9) * Real.exp (-((7 / 6 : ℝ) * U)) := by
  simpa only [lemma56PaperT, lemma23PaperL, lemma23PaperP, lemma56PerronMangoldtSum,
    lemma56PerronMangoldtTerm, lemma56GaussianPhase, lemma56Mangoldt, lemma56PerronWeight] using
      lemma56_uniform_primitive_perron_mangoldt_window_bound

-- Principal modulus one remains included in the actual right-line truncation.
example {B x H : ℝ} (hB : 0 < B) (hx : 0 < x) (hH : 0 < H) (τ : ℝ) :
    ‖lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) B x τ -
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ in -H..H, lemma56PerronArithmeticIntegrand (1 : DirichletCharacter ℂ 1) B x τ ((2 : ℂ) + (t : ℂ) * I))‖ ≤
      (1 / (2 * Real.pi)) * (4 * lemma56GaussianRightConstant * x ^ 2 * (B ^ 2 / H) *
        Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2))) :=
  lemma56_actual_perron_mangoldt_truncation 1 hB hx hH τ

-- Closed oscillatory endpoints of the actual arithmetic estimate.
example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
    (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
      let U := lemma23PaperL D ^ (9 / 2 : ℝ)
      let B := Real.exp ((3 / 2 : ℝ) * U)
      let E := C * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * U))
      ‖lemma56PerronMangoldtSum θ B x (D : ℝ)‖ ≤ E ∧
        ‖lemma56PerronMangoldtSum θ B x (-(D : ℝ))‖ ≤ E := by
  obtain ⟨C, hC, D₀, h⟩ := lemma56_uniform_primitive_perron_mangoldt_window_bound
  refine ⟨C, hC, D₀, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne x hx hxmax
  constructor
  · exact h χ θ hDN hD hA hθ hq1 hqT hne hx hxmax (by simp)
  · exact h χ θ hDN hD hA hθ hq1 hqT hne hx hxmax (by simp)

example {U : ℝ} (hU : 2000 ≤ U) : U ^ 2 + 4 * U + 2 ≤ Real.exp U / 16 :=
  lemma56_perron_supergaussian_budget hU

-- Actual weight bounds and reciprocal reflection, for every real width.
example (B : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ lemma56PerronWeight B x ∧ lemma56PerronWeight B x ≤ 1 ∧
      lemma56PerronWeight B x + lemma56PerronWeight B x⁻¹ = 1 :=
  ⟨lemma56_perron_weight_nonneg B hx, lemma56_perron_weight_le_one B hx,
    lemma56_perron_weight_reflection B hx⟩

example (B : ℝ) : lemma56PerronWeight B 1 = 1 / 2 := by simp [lemma56PerronWeight]

-- A strict integer cutoff excludes its endpoint.
example {q : ℕ} (θ : DirichletCharacter ℂ q) (m : ℕ) (τ : ℝ) :
    lemma56SharpMangoldtTerm θ (m : ℝ) τ m = 0 := by simp [lemma56SharpMangoldtTerm]

example {q : ℕ} (θ : DirichletCharacter ℂ q) {n : ℕ} (hn : n ≠ 0) (B τ : ℝ) :
    lemma56PerronErrorTerm θ B (n : ℝ) τ n =
      (lemma56GaussianPhase τ n * lemma56Mangoldt θ n) * (1 / 2 : ℂ) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [lemma56PerronErrorTerm, div_self hnr, lemma56PerronWeight]

example {B y ε : ℝ} (hB : 0 < B) (hy : 0 < y) (hε : 0 ≤ ε)
    (hdist : ε ≤ |Real.log y|) (hwide : 1 ≤ B * ε) :
    |lemma56PerronWeight B y - (if 1 < y then 1 else 0)| ≤
      (Real.sqrt Real.pi)⁻¹ * y ^ 2 * Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2) :=
  lemma56_perron_weight_step_error_distance_bound hB hy hε hdist hwide

-- Both independently defined actual sums, with the finite strict cutoff expanded.
example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x ε : ℝ} (hB : 0 < B) (hx : 1 ≤ x) (hε : 0 ≤ ε) (hwide : 1 ≤ B * ε) (τ : ℝ) :
    ‖(∑' n : ℕ, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
          (lemma56PerronWeight B (x / (n : ℝ)) : ℂ)) -
      (∑ n ∈ Finset.range ⌈x⌉₊, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)))‖ ≤
      (x * (Real.exp ε - Real.exp (-ε)) + 2) * (Real.log x + ε) +
        lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ * x ^ 2 *
          Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2) := by
  simpa only [lemma56PerronMangoldtSum, lemma56PerronMangoldtTerm, lemma56SharpMangoldtSum,
    lemma56GaussianPhase, lemma56Mangoldt] using
      lemma56_actual_perron_smoothing_error_bound θ hB hx hε hwide τ

example {q : ℕ} (θ : DirichletCharacter ℂ q) (B x τ ε : ℝ) :
    lemma56PerronNearErrorTerm θ B x τ ε 0 = 0 := by
  simp [lemma56PerronNearErrorTerm, lemma56_perron_error_zero]

example {x ε : ℝ} (hx : 0 < x) (hε : 0 ≤ ε) :
    (((Finset.range ⌈x * Real.exp ε⌉₊).filter
      (fun n : ℕ => n ≠ 0 ∧ |Real.log (x / (n : ℝ))| < ε)).card : ℝ) ≤
        x * Real.exp ε - x * Real.exp (-ε) + 2 :=
  lemma56_perron_near_indices_card hx hε

example {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ : ℝ) :
    (∑' n : ℕ, lemma56PerronErrorTerm (1 : DirichletCharacter ℂ 1) B x τ n) =
      lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) B x τ -
        lemma56SharpMangoldtSum (1 : DirichletCharacter ℂ 1) x τ :=
  lemma56_perron_error_term_tsum 1 hB hx τ

example (x : ℝ) : lemma56PerronNearIndices x 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hh := (Finset.mem_filter.mp hn).2.2
  exact (not_lt_of_ge (abs_nonneg _)) hh

#print axioms ZhangLS.Spec.lemma56_mangoldt_majorant_nonneg
#print axioms ZhangLS.Spec.lemma56_mangoldt_majorant_eq_norm_term
#print axioms ZhangLS.Spec.lemma56_mangoldt_majorant_summable
#print axioms ZhangLS.Spec.lemma56_mangoldt_majorant_tsum
#print axioms ZhangLS.Spec.lemma56_mangoldt_norm_le
#print axioms ZhangLS.Spec.lemma56_sharp_mangoldt_term_outside
#print axioms ZhangLS.Spec.lemma56_sharp_mangoldt_term_summable
#print axioms ZhangLS.Spec.lemma56_sharp_mangoldt_term_tsum
#print axioms ZhangLS.Spec.lemma56_perron_error_term_eq_sub
#print axioms ZhangLS.Spec.lemma56_perron_error_term_summable
#print axioms ZhangLS.Spec.lemma56_perron_error_term_tsum
#print axioms ZhangLS.Spec.lemma56_perron_error_zero
#print axioms ZhangLS.Spec.lemma56_perron_error_distance_majorant
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_perron_paper_exterior_bounds
#print axioms ZhangLS.Spec.lemma56_perron_far_error_summable
#print axioms ZhangLS.Spec.lemma56_perron_near_error_summable
#print axioms ZhangLS.Spec.lemma56_perron_far_error_bound
#print axioms ZhangLS.Spec.lemma56_perron_error_near_far
#print axioms ZhangLS.Spec.lemma56_actual_perron_smoothing_error_split
#print axioms ZhangLS.Spec.lemma56_perron_horizontal_point_bound
#print axioms ZhangLS.Spec.lemma56_perron_horizontal_integral_bound
#print axioms ZhangLS.Spec.lemma56_perron_paper_logDeriv_width_budget
#print axioms ZhangLS.Spec.lemma56_perron_paper_horizontal_budget
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_perron_mangoldt_window_bound
#print axioms ZhangLS.Spec.lemma56_perron_near_real_bounds
#print axioms ZhangLS.Spec.lemma56_perron_near_term_outside
#print axioms ZhangLS.Spec.lemma56_perron_near_error_tsum
#print axioms ZhangLS.Spec.lemma56_perron_near_indices_card
#print axioms ZhangLS.Spec.lemma56_perron_error_norm_le_mangoldt
#print axioms ZhangLS.Spec.lemma56_perron_near_error_bound
#print axioms ZhangLS.Spec.lemma56_actual_perron_smoothing_error_bound
#print axioms ZhangLS.Spec.lemma56_perron_supergaussian_budget
#print axioms ZhangLS.Spec.lemma56_perron_paper_scales
#print axioms ZhangLS.Spec.lemma56_perron_paper_right_budget
#print axioms ZhangLS.Spec.lemma56_perron_rectangle_norm_budget
#print axioms ZhangLS.Spec.lemma56_actual_perron_right_eq
#print axioms ZhangLS.Spec.lemma56_actual_perron_right_integrable
#print axioms ZhangLS.Spec.lemma56_actual_perron_right_envelope
#print axioms ZhangLS.Spec.lemma56_actual_perron_right_truncation
#print axioms ZhangLS.Spec.lemma56_actual_perron_mangoldt_truncation
#print axioms ZhangLS.Spec.lemma56_perron_weight_nonneg
#print axioms ZhangLS.Spec.lemma56_perron_weight_reflection
#print axioms ZhangLS.Spec.lemma56_perron_weight_le_one
#print axioms ZhangLS.Spec.lemma56_perron_weight_bounds
#print axioms ZhangLS.Spec.lemma56_perron_endpoint_rescale
#print axioms ZhangLS.Spec.lemma56_perron_weight_lower_tail
#print axioms ZhangLS.Spec.lemma56_perron_weight_upper_tail
#print axioms ZhangLS.Spec.lemma56_perron_weight_step_error
#print axioms ZhangLS.Spec.lemma56_perron_weight_step_error_le_one
#print axioms ZhangLS.Spec.lemma56_perron_weight_step_error_le_gaussian
#print axioms ZhangLS.Spec.lemma56_perron_gaussian_power_majorant
#print axioms ZhangLS.Spec.lemma56_perron_weight_step_error_power_bound
#print axioms ZhangLS.Spec.lemma56_perron_weight_step_error_distance_bound
#print axioms ZhangLS.Spec.lemma56_perron_paper_window_left_budget
#print axioms ZhangLS.Spec.lemma56_uniform_primitive_perron_window_left_bound
