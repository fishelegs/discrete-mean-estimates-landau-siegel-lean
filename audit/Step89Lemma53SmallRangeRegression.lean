import ZhangLS.Spec.Lemma53

/-! The actual original small-x range is proved, including its upper endpoint.
At Step 89 the full target remained open; Step 90 completes both ranges. -/

open Complex MeasureTheory ZhangLS.Spec

set_option maxHeartbeats 1000000

example (D : ℕ) (x a b v : ℝ) :
    (∫ u : ℝ in a..b, lemma53ErrorKernel D x (u : ℂ)) =
      (∫ u : ℝ in a..b, lemma53ErrorKernel D x ((u : ℂ) + (v : ℂ) * I)) +
        I * (∫ y : ℝ in 0..v, lemma53ErrorKernel D x ((a : ℂ) + (y : ℂ) * I)) -
          I * (∫ y : ℝ in 0..v, lemma53ErrorKernel D x ((b : ℂ) + (y : ℂ) * I)) :=
  lemma53_error_rectangle_shift D x a b v

example {D : ℕ} (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x) :
    ‖lemma53PaperDelta D x -
      lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)) -
        (∫ u : ℝ in -lemma53SmallRadius D..lemma53SmallRadius D,
          lemma53ErrorKernel D x (u : ℂ))‖ ≤
      4 * (Real.exp 1 + 1) * Real.exp (-((Real.log D) ^ 10) / 2) :=
  lemma53_small_radius_tail hD hL hx

example {D : ℕ} (hD : 1 < D) (x : ℝ) :
    (∫ u : ℝ,
      ‖lemma53GaussianPhase D x ((u : ℂ) + (lemma53StationaryHeight D x : ℂ) * I)‖) =
        ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ :=
  lemma53_stationary_gaussian_integral hD x

-- The paper's original boundary x=t0^(51/50) is included.
example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) :
    let x := lemma51PaperT0 D ^ (51 / 50 : ℝ)
    ‖lemma53PaperDelta D x -
      lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ ≤
        lemma44PaperAlpha D *
          ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ +
            (4 * (Real.exp 1 + 1) + 2) * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  dsimp only
  apply lemma53_small_range_estimate hD hL
  · unfold lemma51PaperT0
    have : 0 < lemma23PaperL D := by linarith
    positivity
  · exact le_rfl

example : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ x : ℝ, 0 < x →
    x ≤ ((Real.log D) ^ 519) ^ (51 / 50 : ℝ) →
    ‖lemma53PaperDelta D x -
      lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ ≤
      (4 * (Real.exp 1 + 1) + 2) * lemma44PaperAlpha D *
        ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ +
          (4 * (Real.exp 1 + 1) + 2) * Real.exp (-(1 / 2 : ℝ) * (Real.log D) ^ 10) :=
  lemma53_small_range_uniform_threshold

#print axioms lemma53_error_rectangle_shift
#print axioms lemma53_actual_error_integral
#print axioms lemma53_small_radius_tail
#print axioms lemma53_perturbation_rectangle_bound
#print axioms lemma53_gaussian_between_stationary_bound
#print axioms lemma53_stationary_gaussian_integral
#print axioms lemma53_small_contour_radius_bound
#print axioms lemma53_small_contour_error_le_alpha
#print axioms lemma53_small_range_estimate
#print axioms lemma53_small_range_uniform_threshold
