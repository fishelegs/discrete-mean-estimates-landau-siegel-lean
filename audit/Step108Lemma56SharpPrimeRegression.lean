import ZhangLS.Spec.Lemma56PrimeWindowAbsolute

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open ZhangLS.Spec Complex MeasureTheory Finset
open scoped Real

example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) {U x : ℝ}
    (hU : 2000 ≤ U) (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (U ^ 2)) (τ : ℝ) :
    ‖(∑' n : ℕ, (n : ℂ) ^ ((τ : ℂ) * I) *
      (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
      (((1 : ℝ) / 2 + (Real.sqrt Real.pi)⁻¹ *
        ∫ v : ℝ in (0 : ℝ)..Real.exp ((3 / 2 : ℝ) * U) * Real.log (x / (n : ℝ)),
          Real.exp (-(v ^ 2)) : ℝ) : ℂ)) -
      ∑ n ∈ Finset.range ⌈x⌉₊, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))‖ ≤
      lemma56PerronUnsmoothingConstant * Real.exp (U ^ 2) *
        Real.exp (-((7 / 6 : ℝ) * U)) := by
  simpa only [lemma56PerronMangoldtSum, lemma56PerronMangoldtTerm,
    lemma56SharpMangoldtSum, lemma56GaussianPhase, lemma56Mangoldt, lemma56PerronWeight] using
    lemma56_actual_perron_paper_smoothing_error θ hU hx hxmax τ

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
    (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {x τ : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D → |τ| ≤ D →
      ‖∑ n ∈ Finset.range ⌈x⌉₊, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))‖ ≤
        C * lemma23PaperP D *
          Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by
  simpa only [lemma56SharpMangoldtSum, lemma56GaussianPhase, lemma56Mangoldt] using
    lemma56_uniform_primitive_sharp_mangoldt_window_bound

example (θ : DirichletCharacter ℂ 1) {U : ℝ} (hU : 2000 ≤ U)
    (n : ℕ) (hn : 1 ≤ n) (hnmax : (n : ℝ) ≤ 2 * Real.exp (U ^ 2)) (τ : ℝ) :
    ‖lemma56PerronMangoldtSum θ (Real.exp ((3 / 2 : ℝ) * U)) (n : ℝ) τ -
      ∑ k ∈ Finset.range n, (k : ℂ) ^ ((τ : ℂ) * I) *
        (θ (k : ZMod 1) * (ArithmeticFunction.vonMangoldt k : ℂ))‖ ≤
      lemma56PerronUnsmoothingConstant * Real.exp (U ^ 2) *
        Real.exp (-((7 / 6 : ℝ) * U)) := by
  simpa only [lemma56SharpMangoldtSum, lemma56GaussianPhase, lemma56Mangoldt,
    Nat.ceil_natCast] using lemma56_actual_perron_paper_smoothing_error θ hU
      (by exact_mod_cast hn) hnmax τ

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
    (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
      (‖∑ n ∈ Finset.range ⌈x⌉₊, (n : ℂ) ^ ((-(D : ℝ) : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))‖ ≤
        C * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)))) ∧
      (‖∑ n ∈ Finset.range ⌈x⌉₊, (n : ℂ) ^ (((D : ℝ) : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))‖ ≤
        C * lemma23PaperP D * Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)))) := by
  obtain ⟨C, hC, D₀, h⟩ := lemma56_uniform_primitive_sharp_mangoldt_window_bound
  refine ⟨C, hC, D₀, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne x hx hxmax
  constructor
  · simpa only [lemma56SharpMangoldtSum, lemma56GaussianPhase, lemma56Mangoldt, Complex.ofReal_neg] using
      h χ θ hDN hD hA hθ hq1 hqT hne hx hxmax
        (τ := -(D : ℝ)) (by simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ D)])
  · simpa only [lemma56SharpMangoldtSum, lemma56GaussianPhase, lemma56Mangoldt] using
      h χ θ hDN hD hA hθ hq1 hqT hne hx hxmax
        (τ := (D : ℝ)) (by simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ D)])


example {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) (τ : ℝ) :
    ‖(∑ n ∈ Finset.range ⌈x⌉₊, (n : ℂ) ^ ((τ : ℂ) * I) *
      (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))) -
      ∑ n ∈ Finset.range ⌈x⌉₊, if n.Prime then
        (n : ℂ) ^ ((τ : ℂ) * I) * (θ (n : ZMod q) * (Real.log (n : ℝ) : ℂ)) else 0‖ ≤
      2 * Real.sqrt x * Real.log x := by
  simpa only [lemma56SharpMangoldtSum, lemma56SharpPrimeLogSum,
    lemma56GaussianPhase, lemma56Mangoldt] using
    lemma56_actual_sharp_prime_power_bound θ hx τ

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
    (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ {x τ : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D → |τ| ≤ D →
      ‖∑ n ∈ Finset.range ⌈x⌉₊, if n.Prime then
        (n : ℂ) ^ ((τ : ℂ) * I) * (θ (n : ZMod q) * (Real.log (n : ℝ) : ℂ)) else 0‖ ≤
        C * lemma23PaperP D *
          Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by
  simpa only [lemma56SharpPrimeLogSum] using
    lemma56_uniform_primitive_sharp_prime_log_window_bound

example (θ : DirichletCharacter ℂ 1) (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) :
    ‖(∑ k ∈ Finset.range n, (k : ℂ) ^ ((τ : ℂ) * I) *
      (θ (k : ZMod 1) * (ArithmeticFunction.vonMangoldt k : ℂ))) -
      ∑ k ∈ Finset.range n, if k.Prime then
        (k : ℂ) ^ ((τ : ℂ) * I) * (θ (k : ZMod 1) * (Real.log (k : ℝ) : ℂ)) else 0‖ ≤
      2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  simpa only [lemma56SharpMangoldtSum, lemma56SharpPrimeLogSum,
    lemma56GaussianPhase, lemma56Mangoldt, Nat.ceil_natCast] using
    lemma56_actual_sharp_prime_power_bound θ (by exact_mod_cast hn : (1 : ℝ) ≤ n) τ

example {q : ℕ} (θ : DirichletCharacter ℂ q) (τ : ℝ) :
    (∑ n ∈ Finset.range ⌈(1 : ℝ)⌉₊, (n : ℂ) ^ ((τ : ℂ) * I) *
      (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))) = 0 ∧
    (∑ n ∈ Finset.range ⌈(1 : ℝ)⌉₊, if n.Prime then
      (n : ℂ) ^ ((τ : ℂ) * I) * (θ (n : ZMod q) * (Real.log (n : ℝ) : ℂ)) else 0) = 0 := by
  simp


#print axioms lemma56_perron_exp_window_bound
#print axioms lemma56_perron_unsmoothing_scales
#print axioms lemma56_perron_unsmoothing_far_margin
#print axioms lemma56_perron_unsmoothing_polynomial
#print axioms lemma56_perron_unsmoothing_polynomial_decay
#print axioms lemma56_perron_unsmoothing_endpoint_budget
#print axioms lemma56_perron_unsmoothing_near_budget
#print axioms lemma56_perron_unsmoothing_far_budget
#print axioms lemma56_perron_unsmoothing_constant_pos
#print axioms lemma56_actual_perron_paper_smoothing_error
#print axioms lemma56_uniform_primitive_sharp_mangoldt_window_bound
#print axioms lemma56_actual_sharp_prime_power_difference
#print axioms lemma56_actual_sharp_prime_power_norm
#print axioms lemma56_actual_sharp_prime_power_bound
#print axioms lemma56_actual_prime_power_paper_budget
#print axioms lemma56_actual_paper_prime_power_error
#print axioms lemma56_uniform_primitive_sharp_prime_log_window_bound

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
    (q : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ)) →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
    ∀ τ : ℝ, |τ| ≤ D →
      ‖∑ p ∈ (range ⌈Real.exp ((Real.log (D : ℝ)) ^ 9) *
        (1 + (Real.log (D : ℝ)) ^ (-68 : ℤ))⌉₊).filter
          (fun p : ℕ => p.Prime ∧ Real.exp ((Real.log (D : ℝ)) ^ 9) < (p : ℝ) ∧
            (p : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ 9) *
              (1 + (Real.log (D : ℝ)) ^ (-68 : ℤ))),
        θ (p : ZMod q) * (p : ℂ) ^ (1 + I * (τ : ℂ))‖ ≤
          C * (Real.exp ((Real.log (D : ℝ)) ^ 9)) ^ 2 *
            Real.exp (-((7 / 6 : ℝ) * (Real.log (D : ℝ)) ^ (9 / 2 : ℝ))) := by
  simpa only [lemma56PrimeSum, lemma56PaperPrimes, lemma56PrimeUpper,
    lemma56PaperT, lemma23PaperP, lemma23PaperL] using
    lemma56_uniform_primitive_prime_window_absolute_bound

example {p : ℕ} (hp : p.Prime) (τ : ℝ) :
    (1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (1 + I * (τ : ℂ)) =
      ((p : ℝ) / Real.log (p : ℝ)) • ((p : ℂ) ^ ((τ : ℂ) * I) *
        ((1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (Real.log (p : ℝ) : ℂ))) :=
  lemma56_actual_prime_weight_identity _ hp τ

example {D q : ℕ} (θ : DirichletCharacter ℂ q) (τ : ℝ) :
    (∑ p ∈ lemma56PaperPrimes D, θ (p : ZMod q) * (p : ℂ) ^ (1 + I * (τ : ℂ))) =
      ∑ n ∈ Ico (⌊lemma23PaperP D⌋₊ + 1) ⌈lemma56PrimeUpper D⌉₊,
        if n.Prime then θ (n : ZMod q) * (n : ℂ) ^ (1 + I * (τ : ℂ)) else 0 := by
  exact lemma56_actual_paper_prime_interval θ (Real.exp_pos _).le τ

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
    (q : ℝ) < lemma56PaperT D →
    (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      (‖∑ p ∈ lemma56PaperPrimes D, θ (p : ZMod q) *
          (p : ℂ) ^ (1 + I * (-(D : ℝ) : ℂ))‖ ≤
        C * (lemma23PaperP D) ^ 2 * Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)))) ∧
      (‖∑ p ∈ lemma56PaperPrimes D, θ (p : ZMod q) *
          (p : ℂ) ^ (1 + I * (((D : ℝ) : ℂ)))‖ ≤
        C * (lemma23PaperP D) ^ 2 * Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)))) := by
  obtain ⟨C, hC, D₀, h⟩ := lemma56_uniform_primitive_prime_window_absolute_bound
  refine ⟨C, hC, D₀, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne
  constructor
  · simpa only [lemma56PrimeSum, Complex.ofReal_neg] using
      h χ θ hDN hD hA hθ hq1 hqT hne (-(D : ℝ))
        (by simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ D)])
  · simpa only [lemma56PrimeSum] using
      h χ θ hDN hD hA hθ hq1 hqT hne (D : ℝ)
        (by simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ D)])


#print axioms lemma56_finite_abel_positive_budget
#print axioms lemma56_prime_weight_mono
#print axioms lemma56_actual_prime_weight_identity
#print axioms lemma56_actual_paper_prime_interval
#print axioms lemma56_paper_prime_weight_parameters
#print axioms lemma56_actual_paper_prime_weight_budget
#print axioms lemma56_uniform_primitive_prime_window_absolute_bound
