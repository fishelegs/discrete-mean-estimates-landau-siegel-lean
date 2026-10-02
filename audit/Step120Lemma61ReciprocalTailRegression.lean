import ZhangLS.Spec.Lemma61ReciprocalTailTruncation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p) {z : ℂ} (hz : 1 < z.re) :
    DirichletCharacter.LFunction ψ z =
      (∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
        (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
        ψ (n : ZMod p) * Complex.exp (-z * (Real.log (n : ℝ) : ℂ))) +
      ∑' n : ℕ, if lemma56PaperT D ^ 3 ≤ (n : ℝ) then
        LSeries.term (fun m => ψ (m : ZMod p)) z n else 0 := by
  exact lemma61_actual_reciprocal_series_split ψ hz

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    lemma44GeneralRectangleBoundaryIntegral
      (fun w => lemma23DirichletZ ψ (s + w) *
        (∑' n : ℕ, if lemma56PaperT D ^ 3 ≤ (n : ℝ) then
          LSeries.term (fun m => ψ⁻¹ (m : ZMod p)) (1 - s - w) n else 0) *
        Complex.exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) * lemma57OmegaOne D w / w)
      (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20) = 0 := by
  exact lemma61_actual_reciprocal_tail_rectangle_cauchy ψ hψ hL hs

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ} (hL : 64 ≤ lemma23PaperL D)
    (hre : |s.re - 1 / 2| < 2 * lemma44PaperAlpha D)
    (him : |s.im - 2 * Real.pi * lemma23PaperL D ^ 519| < lemma23PaperL D ^ 405 + 2) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma23DirichletZ ψ (s + ((-1 : ℂ) + (v : ℂ) * I)) *
          (∑' n : ℕ, if lemma56PaperT D ^ 3 ≤ (n : ℝ) then
            LSeries.term (fun m => ψ⁻¹ (m : ZMod p)) (1 - s - ((-1 : ℂ) + (v : ℂ) * I)) n else 0) *
          Complex.exp (((-1 : ℂ) + (v : ℂ) * I) * (Real.log (lemma61PaperP4 D) : ℂ)) *
          lemma57OmegaOne D ((-1 : ℂ) + (v : ℂ) * I) / ((-1 : ℂ) + (v : ℂ) * I) * I)‖ ≤
      (2 * Real.exp (2 + 4 * Real.pi) * (lemma44InverseSquareMass + lemma61QuarterSeriesMass)) *
        Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  apply lemma61_actual_reciprocal_tail_truncation_bound ψ hψ hL
  exact ⟨hre,by simpa [lemma23PaperCenter] using him⟩
end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma61_region_quarter_bounds
#print axioms ZhangLS.Spec.lemma61_large_shift_rectangle_bounds
#print axioms ZhangLS.Spec.lemma61_wide_log_modulus_error_le_one
#print axioms ZhangLS.Spec.lemma61_P4_PT0_log_identity
#print axioms ZhangLS.Spec.lemma61_actual_Z_P4_cancellation
#print axioms ZhangLS.Spec.lemma61_large_shift_gaussian_bound
#print axioms ZhangLS.Spec.lemma61_large_shift_denominator_bound
#print axioms ZhangLS.Spec.lemma61_T_log_bounds
#print axioms ZhangLS.Spec.lemma61_reciprocal_tail_summable
#print axioms ZhangLS.Spec.lemma61_actual_reciprocal_series_split
#print axioms ZhangLS.Spec.lemma61_reciprocal_far_left_term_bound
#print axioms ZhangLS.Spec.lemma61_reciprocal_far_left_sum_bound
#print axioms ZhangLS.Spec.lemma61_far_left_exponent_bound
#print axioms ZhangLS.Spec.lemma61_actual_far_left_tail_point_bound
#print axioms ZhangLS.Spec.lemma61_far_left_integral_exponent_absorption
#print axioms ZhangLS.Spec.lemma61_actual_far_left_tail_integral_bound
#print axioms ZhangLS.Spec.lemma61_actual_reciprocal_tail_rectangle_differentiable
#print axioms ZhangLS.Spec.lemma61_actual_reciprocal_tail_rectangle_cauchy
#print axioms ZhangLS.Spec.lemma61_quarter_series_summable
#print axioms ZhangLS.Spec.lemma61_reciprocal_horizontal_term_bound
#print axioms ZhangLS.Spec.lemma61_reciprocal_horizontal_sum_bound
#print axioms ZhangLS.Spec.lemma61_actual_horizontal_tail_point_bound
#print axioms ZhangLS.Spec.lemma61_actual_horizontal_tail_integral_bound
#print axioms ZhangLS.Spec.lemma61_actual_reciprocal_tail_truncation_bound
