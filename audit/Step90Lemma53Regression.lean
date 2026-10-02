import ZhangLS.Spec.Lemma53

/-! The full original two-range statement, actual Mellin definition,
signed downward shift, right-end limit, and standard axiom dependencies. -/

open Complex MeasureTheory ZhangLS.Spec Filter Set
open scoped Topology

set_option maxHeartbeats 1000000

example : Lemma53Target := lemma53_proved

-- One C, k and natural threshold precede all D and x. The original
-- noninteger powers and both distinct exponential tails are retained.
example : ∃ C : ℝ, 0 < C ∧ ∃ k : ℝ, 0 < k ∧ ∃ D₀ : ℕ,
    ∀ D : ℕ, D₀ ≤ D → ∀ x : ℝ, 0 < x →
      (x ≤ ((Real.log D) ^ 519) ^ (51 / 50 : ℝ) →
        ‖lemma53PaperDelta D x -
          lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ ≤
            C * lemma44PaperAlpha D *
              ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ +
            C * Real.exp (-k * (Real.log D) ^ 10)) ∧
      (((Real.log D) ^ 519) ^ (51 / 50 : ℝ) < x →
        ‖lemma53PaperDelta D x‖ ≤ C *
          (Real.exp (-(((Real.log D) ^ 400 * Real.log x / 100) ^ 2)) +
            Real.exp (-(x ^ (99 / 100 : ℝ)) / (Real.log D) ^ 400))) :=
  lemma53_proved

example (D : ℕ) (x : ℝ) : lemma53PaperDelta D x =
    mellinInv (3 / 2) (fun s => lemma53PaperThetaStar s * lemma53PaperOmega D s) x *
      Complex.exp ((2 * Real.pi : ℂ) * I * (x : ℂ)) := rfl

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {x : ℝ}
    (hx : 0 < x) (hxhi : ((Real.log D) ^ 519) ^ (51 / 50 : ℝ) < x) :
    ‖lemma53PaperDelta D x‖ ≤
      (2 + Real.exp 1) * Real.exp (-(((Real.log D) ^ 400 * Real.log x / 100) ^ 2)) +
        (Real.sqrt Real.pi * Real.exp 2) *
          Real.exp (-(x ^ (99 / 100 : ℝ)) / (Real.log D) ^ 400) :=
  lemma53_large_range_estimate hD hL hx hxhi

example {D : ℕ} (hB : 1 ≤ lemma53PaperScale D) {x : ℝ}
    (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) :
    Tendsto (fun R : ℝ => ∫ v : ℝ in 0..(-1 / lemma53PaperScale D),
      lemma53OscillatoryKernel D x ((R : ℂ) + (v : ℂ) * I)) atTop (𝓝 0) :=
  lemma53_large_right_vertical_tendsto_zero hB hx hX ht

-- The norm estimate includes v=0; it does not divide the phase by v.
example {D : ℕ} (hB : 1 ≤ lemma53PaperScale D) {x u : ℝ}
    (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) (hu : lemma53LargeEndpoint x ≤ u) :
    ‖lemma53OscillatoryKernel D x (u : ℂ)‖ ≤
      Real.exp (1 + u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) := by
  simpa only [ofReal_zero, zero_mul, add_zero, mul_zero] using
    lemma53_large_shifted_norm_bound hB hx hX ht hu (v := 0) (by simp)

#print axioms lemma53_large_range_parameters
#print axioms lemma53_large_endpoint_exponential
#print axioms lemma53_large_shifted_norm_bound
#print axioms lemma53_real_envelope_integral
#print axioms lemma53_large_left_tail_bound
#print axioms lemma53_large_left_vertical_bound
#print axioms lemma53_large_ray_integrable
#print axioms lemma53_large_right_ray_bound
#print axioms lemma53_large_right_vertical_tendsto_zero
#print axioms lemma53_large_infinite_contour_shift
#print axioms lemma53_large_range_estimate
#print axioms lemma53_proved
