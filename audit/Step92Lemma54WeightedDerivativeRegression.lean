import ZhangLS.Spec.Lemma54

/-! Regression for actual weighted derivative contours and integrations by parts.
The uniform polynomial moment and disk normalization in Lemma54Target remain open. -/

open Complex MeasureTheory ZhangLS.Spec Filter Set Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000

-- The complete original large-x domain, actual derivative operators and scales.
example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D)
    {x : ℝ} (hx : 0 < x) (hxhi : ((Real.log D) ^ 519) ^ (51 / 50 : ℝ) < x) :
    ‖deriv (lemma53PaperDelta D) x‖ ≤
      (1 + 8 * Real.pi ^ 2) * (4 + 2 * Real.exp 1) *
        Real.exp (-((((Real.log D) ^ 400) * Real.log x / 100) ^ 2)) +
      2 * (1 + 8 * Real.pi ^ 2) * Real.sqrt Real.pi * Real.exp 3 *
        Real.exp (-(x ^ (99 / 100 : ℝ)) / (Real.log D) ^ 400) ∧
    ‖deriv (deriv (lemma53PaperDelta D)) x‖ ≤
      (1 + 8 * Real.pi ^ 2) * (4 + 2 * Real.exp 1) *
        Real.exp (-((((Real.log D) ^ 400) * Real.log x / 100) ^ 2)) +
      2 * (1 + 8 * Real.pi ^ 2) * Real.sqrt Real.pi * Real.exp 3 *
        Real.exp (-(x ^ (99 / 100 : ℝ)) / (Real.log D) ^ 400) :=
  ⟨lemma54_actual_first_deriv_large_range hD hL hx hxhi,
    lemma54_actual_second_deriv_large_range hD hL hx hxhi⟩

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {a : ℝ} (ha : 0 < a) :
    deriv (lemma53PaperDelta D) =O[atTop] (fun x : ℝ => x ^ (-a)) ∧
      deriv (deriv (lemma53PaperDelta D)) =O[atTop] (fun x : ℝ => x ^ (-a)) :=
  ⟨lemma54_actual_first_deriv_isBigO_atTop hD hL ha,
    lemma54_actual_second_deriv_isBigO_atTop hD hL ha⟩

-- All four endpoint products used by the two integrations by parts vanish.
example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * lemma53PaperDelta D x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * lemma53PaperDelta D x) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ (s + 1) * deriv (lemma53PaperDelta D) x)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ (s + 1) * deriv (lemma53PaperDelta D) x)
      atTop (𝓝 0) := by
  have hb := lemma54_actual_delta_boundary_products hD hL hs
  have hb' := lemma54_actual_first_deriv_boundary_products hD hL
    (s := s + 1) (by simp only [add_re, one_re]; linarith)
  exact ⟨hb.1, hb.2, hb'.1, hb'.2⟩

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {s : ℂ} (hs : 0 < s.re) :
    lemma54PaperDeltaMellin D s =
      (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s + 1) * deriv (deriv (lemma53PaperDelta D)) x) /
        (s * (s + 1)) :=
  lemma54_actual_mellin_twice_by_parts_div hD hL hs

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => x ^ (s.re + 1) * ‖deriv (deriv (lemma53PaperDelta D)) x‖)
      (Ioi 0) ∧
    ‖mellin (lemma53PaperDelta D) s‖ ≤
      (∫ x : ℝ in Ioi 0, x ^ (s.re + 1) * ‖deriv (deriv (lemma53PaperDelta D)) x‖) / ‖s‖ ^ 2 :=
  ⟨lemma54_actual_second_moment_integrable hD hL hs,
    lemma54_actual_mellin_norm_bound_by_second_moment hD hL hs⟩

#print axioms lemma54_weighted_kernel_integrable
#print axioms lemma54_weighted_left_tail_bound
#print axioms lemma54_weighted_left_vertical_bound
#print axioms lemma54_weighted_right_ray_bound
#print axioms lemma54_weighted_right_vertical_tendsto_zero
#print axioms lemma54_weighted_infinite_contour_shift
#print axioms lemma54_actual_first_deriv_large_range
#print axioms lemma54_actual_second_deriv_large_range
#print axioms lemma54_actual_first_deriv_isBigO_atTop
#print axioms lemma54_actual_second_deriv_isBigO_atTop
#print axioms lemma54_first_deriv_mellin_convergent
#print axioms lemma54_second_deriv_mellin_convergent
#print axioms lemma54_actual_delta_boundary_products
#print axioms lemma54_actual_first_deriv_boundary_products
#print axioms lemma54_actual_mellin_twice_by_parts_div
#print axioms lemma54_actual_second_moment_integrable
#print axioms lemma54_actual_mellin_norm_bound_by_second_moment
