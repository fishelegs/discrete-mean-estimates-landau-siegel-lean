import ZhangLS.Spec.Lemma56PrincipalMassSharpPrime

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
      ‖(∑ n ∈ Finset.range ⌈x⌉₊, if n.Prime then (Real.log (n : ℝ) : ℂ) else 0) -
        ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
        lemma56PrincipalSharpPrimeErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  simpa only [lemma56SharpPrimeLogSum, ofReal_zero, zero_mul, Complex.cpow_zero,
    lemma56_principal_one_apply_nat, one_mul] using lemma56_uniform_principal_sharp_prime_mass_main_error

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
      ‖(∑ n ∈ Finset.range ⌈x⌉₊, (ArithmeticFunction.vonMangoldt n : ℂ)) -
        ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
        lemma56PrincipalSharpMangoldtErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  simpa only [lemma56SharpMangoldtSum, lemma56GaussianPhase, lemma56Mangoldt,
    ofReal_zero, zero_mul, Complex.cpow_zero, lemma56_principal_one_apply_nat,
    one_mul] using lemma56_uniform_principal_sharp_mangoldt_mass_main_error

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
    ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
      ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (lemma56PerronWeight (Real.exp (lemma23PaperL D / 3)) (x / (n : ℝ)) : ℂ)) -
        ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
        lemma56PrincipalMassErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-197 : ℤ) := by
  simpa only [lemma56PerronMangoldtSum, lemma56PerronMangoldtTerm, lemma56GaussianPhase,
    lemma56Mangoldt, ofReal_zero, zero_mul, Complex.cpow_zero,
    lemma56_principal_one_apply_nat, one_mul] using lemma56_uniform_principal_smoothed_mass_main_error

example {D q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    (hL : 10000000 ≤ lemma23PaperL D) {x : ℝ} (hx : 1 ≤ x)
    (hxmax : x ≤ 2 * lemma23PaperP D) (τ : ℝ) :
    ‖(∑' n : ℕ, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
          (lemma56PerronWeight (Real.exp (lemma23PaperL D / 3)) (x / (n : ℝ)) : ℂ)) -
      (∑ n ∈ Finset.range ⌈x⌉₊, (n : ℂ) ^ ((τ : ℂ) * I) *
        (θ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)))‖ ≤
      lemma56PrincipalUnsmoothingConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  simpa only [lemma56PerronMangoldtSum, lemma56PerronMangoldtTerm,
    lemma56SharpMangoldtSum, lemma56GaussianPhase, lemma56Mangoldt] using
      lemma56_actual_principal_mass_smoothing_removal θ hL hx hxmax τ

example : ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ‖(∑ n ∈ Finset.range ⌈2 * lemma23PaperP D⌉₊,
          if n.Prime then (Real.log (n : ℝ) : ℂ) else 0) -
        ((2 * lemma23PaperP D * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
        lemma56PrincipalSharpPrimeErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  obtain ⟨Dm, hm⟩ := lemma56_uniform_principal_sharp_prime_mass_main_error
  obtain ⟨Ds, hs⟩ := lemma56_uniform_principal_mass_scale_threshold
  refine ⟨max Dm Ds, ?_⟩
  intro D χ hDN hD hA
  have hL := hs D ((le_max_right _ _).trans hDN)
  have hp : 1 ≤ lemma23PaperP D := Real.one_le_exp (pow_nonneg (by linarith only [hL]) 9)
  simpa only [lemma56SharpPrimeLogSum, ofReal_zero, zero_mul, Complex.cpow_zero,
    lemma56_principal_one_apply_nat, one_mul] using
      hm χ ((le_max_left _ _).trans hDN) hD hA (by linarith only [hp] : 1 ≤ 2 * lemma23PaperP D) le_rfl

example {L : ℝ} (hL : 10000000 ≤ L) :
    L ^ 3 * Real.exp (-(L ^ 8)) ≤ L ^ (-197 : ℤ) ∧
      Real.exp (-L / 4) ≤ L ^ (-200 : ℤ) ∧
        Real.exp (2 / (Real.exp (L / 3)) ^ 2 -
          (Real.exp (L / 3)) ^ 2 * (Real.exp (-L / 4)) ^ 2 / 2) ≤ Real.exp (-2 * L ^ 9) :=
  ⟨lemma56_principal_mass_polynomial_absorption hL,
    (lemma56_principal_mass_smoothing_polynomial hL).1,
    lemma56_principal_mass_far_smoothing_gaussian hL⟩

#print axioms lemma56_principal_mass_exp_base
#print axioms lemma56_principal_mass_exp_power
#print axioms lemma56_principal_mass_left_power
#print axioms lemma56_principal_mass_moment_budget
#print axioms lemma56_principal_mass_scale_parameters
#print axioms lemma56_principal_mass_left_budget
#print axioms lemma56_principal_mass_height_exponent
#print axioms lemma56_principal_mass_horizontal_exponent_identity
#print axioms lemma56_principal_mass_horizontal_gaussian_budget
#print axioms lemma56_principal_mass_horizontal_budget
#print axioms lemma56_principal_mass_error_constant_pos
#print axioms lemma56_principal_mass_main_error_budget
#print axioms lemma56_principal_mass_polynomial_absorption
#print axioms lemma56_uniform_principal_mass_scale_threshold
#print axioms lemma56_uniform_principal_smoothed_mass_main_error
#print axioms lemma56_principal_mass_smoothing_parameters
#print axioms lemma56_principal_mass_smoothing_polynomial
#print axioms lemma56_principal_mass_near_smoothing_budget
#print axioms lemma56_principal_mass_far_smoothing_margin
#print axioms lemma56_principal_mass_far_smoothing_gaussian
#print axioms lemma56_principal_mass_far_smoothing_budget
#print axioms lemma56_principal_unsmoothing_constant_pos
#print axioms lemma56_actual_principal_mass_smoothing_removal
#print axioms lemma56_principal_sharp_mangoldt_error_constant_pos
#print axioms lemma56_uniform_principal_sharp_mangoldt_mass_main_error
#print axioms lemma56_principal_mass_prime_power_decay
#print axioms lemma56_actual_principal_mass_prime_power_error
#print axioms lemma56_principal_sharp_prime_error_constant_pos
#print axioms lemma56_uniform_principal_sharp_prime_mass_main_error

end ZhangLS.Spec
