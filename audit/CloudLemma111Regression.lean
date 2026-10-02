import ZhangLS.Spec.Lemma111

/-!
# Independent regression for the original Lemma 11.1

Source: Zhang, arXiv:2211.02515v1, (2.28), §11, Lemma 11.1 (11.2)–(11.3).
This expands the actual tent, the untruncated Gaussian smoothing integrals,
both closed interior intervals and all three open breakpoint neighborhoods.
No approximation bound is supplied as an assumption.
-/

open MeasureTheory
open scoped Real
open ZhangLS.Spec

example :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      let L := Real.log (D : ℝ)
      let P := Real.exp (L ^ 9)
      ∀ y : ℝ,
        let u := Real.log y / Real.log P
        let f := if u < 1 / 2 then 0
          else if u ≤ 251 / 500 then 500 * (u - 1 / 2)
          else if u ≤ 63 / 125 then 500 * (63 / 125 - u) else 0
        let g := -500 * (∫ z in (1 / 2 : ℝ)..(251 / 500 : ℝ),
            zhangGaussianWeight D (P ^ z / y)) +
          500 * (∫ z in (251 / 500 : ℝ)..(63 / 125 : ℝ),
            zhangGaussianWeight D (P ^ z / y))
        (((P ^ (1 / 2 : ℝ) * Real.exp (L ^ (-10 : ℤ)) ≤ y ∧
            y ≤ P ^ (251 / 500 : ℝ) * Real.exp (-(L ^ (-10 : ℤ)))) ∨
          (P ^ (251 / 500 : ℝ) * Real.exp (L ^ (-10 : ℤ)) ≤ y ∧
            y ≤ P ^ (63 / 125 : ℝ) * Real.exp (-(L ^ (-10 : ℤ))))) →
          |f - g| ≤ C * Real.exp (-c * L ^ 10)) ∧
        ((((P ^ (1 / 2 : ℝ) * Real.exp (-(L ^ (-10 : ℤ))) < y ∧
            y < P ^ (1 / 2 : ℝ) * Real.exp (L ^ (-10 : ℤ))) ∨
          (P ^ (251 / 500 : ℝ) * Real.exp (-(L ^ (-10 : ℤ))) < y ∧
            y < P ^ (251 / 500 : ℝ) * Real.exp (L ^ (-10 : ℤ)))) ∨
          (P ^ (63 / 125 : ℝ) * Real.exp (-(L ^ (-10 : ℤ))) < y ∧
            y < P ^ (63 / 125 : ℝ) * Real.exp (L ^ (-10 : ℤ)))) →
          |f - g| ≤ C * L ^ (-10 : ℤ)) := by
  simpa only [Lemma111Target, Lemma111Interior, Lemma111Transition,
    lemma111Tent, lemma111SmoothedOne, lemma111EtaPlus, lemma111EtaMinus,
    lemma23PaperP, lemma23PaperL, Set.mem_union, Set.mem_Icc, Set.mem_Ioo]
    using lemma111_proved

/-- Both constants in the proved quantitative version are positive. -/
example : (0 : ℝ) < 4000 ∧ (0 : ℝ) < 1 := by norm_num

example {D : ℕ} (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) {y : ℝ}
    (hy : Lemma111Interior D y) :
    |lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) -
      lemma111SmoothedOne D y| ≤ 4000 * Real.exp (-(lemma23PaperL D ^ 10)) :=
  lemma111_interior_bound hD hL hy

example {D : ℕ} (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) {y : ℝ}
    (hy : Lemma111Transition D y) :
    |lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) -
      lemma111SmoothedOne D y| ≤ 4000 * lemma23PaperL D ^ (-10 : ℤ) :=
  lemma111_transition_bound hD hL hy

example : lemma111Tent (1 / 2) = 0 := by norm_num [lemma111Tent]
example : lemma111Tent (251 / 500) = 1 := by norm_num [lemma111Tent]
example : lemma111Tent (63 / 125) = 0 := by norm_num [lemma111Tent]

/-- The shifted second weight retains the `D t₀` factor and exact four endpoints. -/
example (D : ℕ) (y : ℝ) : lemma111SmoothedTwo D y =
    -500 * (∫ z in (62 / 125 : ℝ)..(249 / 500 : ℝ),
      zhangGaussianWeight D (lemma23PaperP D ^ z * (D : ℝ) * lemma23PaperL D ^ 519 / y)) +
    500 * (∫ z in (249 / 500 : ℝ)..(1 / 2 : ℝ),
      zhangGaussianWeight D (lemma23PaperP D ^ z * (D : ℝ) * lemma23PaperL D ^ 519 / y)) := rfl

#print axioms ZhangLS.Spec.lemma111_scale_pos
#print axioms ZhangLS.Spec.lemma111_endpoint
#print axioms ZhangLS.Spec.lemma111_profile_formula
#print axioms ZhangLS.Spec.lemma111_profile_nonneg
#print axioms ZhangLS.Spec.lemma111_profile_complement
#print axioms ZhangLS.Spec.lemma111_profile_le_one
#print axioms ZhangLS.Spec.lemma111_profile_hasDerivAt
#print axioms ZhangLS.Spec.lemma111_profile_continuous
#print axioms ZhangLS.Spec.lemma111_primitive_hasDerivAt
#print axioms ZhangLS.Spec.lemma111_integral_profile
#print axioms ZhangLS.Spec.lemma111_reflected_integral
#print axioms ZhangLS.Spec.lemma111_sqrt_pi_ge_one
#print axioms ZhangLS.Spec.lemma111_negative_weighted_tail
#print axioms ZhangLS.Spec.lemma111_linear_primitive_error
#print axioms ZhangLS.Spec.lemma111_primitive_error
#print axioms ZhangLS.Spec.lemma111_primitive_error_uniform
#print axioms ZhangLS.Spec.lemma111_primitive_error_away
#print axioms ZhangLS.Spec.lemma111_tent_second_difference
#print axioms ZhangLS.Spec.lemma111_weight_log_coordinate
#print axioms ZhangLS.Spec.lemma111_smoothed_second_difference
#print axioms ZhangLS.Spec.lemma111_second_difference_error
#print axioms ZhangLS.Spec.lemma111_smoothed_uniform_bound
#print axioms ZhangLS.Spec.lemma111_scaled_log_displacement
#print axioms ZhangLS.Spec.lemma111_scale_eta
#print axioms ZhangLS.Spec.lemma111_lower_log_gap
#print axioms ZhangLS.Spec.lemma111_upper_log_gap
#print axioms ZhangLS.Spec.lemma111_interior_pos
#print axioms ZhangLS.Spec.lemma111_transition_pos
#print axioms ZhangLS.Spec.lemma111_interior_separation
#print axioms ZhangLS.Spec.lemma111_interior_bound
#print axioms ZhangLS.Spec.lemma111_transition_bound
#print axioms ZhangLS.Spec.lemma111_proved
