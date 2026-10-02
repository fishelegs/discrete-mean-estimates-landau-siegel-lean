import ZhangLS.Spec.Lemma61OriginalLeftError

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) (hσ : s.re = 1 / 2) :
    IntervalIntegrable (fun v : ℝ => lemma61ActualZErrorIntegrand (D := D) ψ s (I * (v : ℂ)))
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  simpa [lemma61ErrorContourShift,hσ] using lemma61_actual_error_path_interval_integrable ψ hL hs

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma61ActualZErrorIntegrand (D := D) ψ s ((-1 : ℂ) + (v : ℂ) * I) * I) =
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ActualZErrorIntegrand (D := D) ψ s (((1 - 2 * s.re : ℝ) : ℂ) + I * (v : ℂ)) * I) +
      (∫ x : ℝ in (-1 : ℝ)..(1 - 2 * s.re),
        lemma61ActualZErrorIntegrand (D := D) ψ s ((x : ℂ) - ((lemma23PaperL D ^ 20 : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in (-1 : ℝ)..(1 - 2 * s.re),
        lemma61ActualZErrorIntegrand (D := D) ψ s ((x : ℂ) + ((lemma23PaperL D ^ 20 : ℝ) : ℂ) * I)) := by
  exact lemma61_actual_error_line_shift ψ hL hs

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ} (hL : 64 ≤ lemma23PaperL D)
    (hre : |s.re - 1 / 2| < 2 * lemma44PaperAlpha D)
    (him : |s.im - 2 * Real.pi * lemma23PaperL D ^ 519| < lemma23PaperL D ^ 405 + 2) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      ((lemma23DirichletZ ψ (s + ((-1 : ℂ) + (v : ℂ) * I)) - lemma23DirichletZ ψ s *
        ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-((-1 : ℂ) + (v : ℂ) * I))) / ((-1 : ℂ) + (v : ℂ) * I)) *
        lemma61ShortPolynomial D ψ⁻¹ (1 - s - ((-1 : ℂ) + (v : ℂ) * I)) *
        Complex.exp (((-1 : ℂ) + (v : ℂ) * I) * (Real.log (lemma61PaperP4 D) : ℂ)) *
        lemma57OmegaOne D ((-1 : ℂ) + (v : ℂ) * I) * I)‖ ≤
      (35 * Real.exp (246 * Real.pi + 1) + 16 * Real.exp (2 + 4 * Real.pi)) *
        lemma61ActualE1 D ψ s (1 / 8) := by
  apply lemma61_actual_original_left_Z_error_bound ψ hψ hL
  exact ⟨hre,by simpa [lemma23PaperCenter] using him⟩
end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma61_positive_real_cpow_model
#print axioms ZhangLS.Spec.lemma61_error_difference_at_zero
#print axioms ZhangLS.Spec.lemma61_error_regular_eq_actual_of_ne_zero
#print axioms ZhangLS.Spec.lemma61_error_difference_rectangle_differentiable
#print axioms ZhangLS.Spec.lemma61_error_regular_rectangle_differentiable
#print axioms ZhangLS.Spec.lemma61_error_vertical_ae_eq
#print axioms ZhangLS.Spec.lemma61_error_vertical_interval_integrable
#print axioms ZhangLS.Spec.lemma61_error_vertical_integral_eq
#print axioms ZhangLS.Spec.lemma61_actual_error_path_interval_integrable
#print axioms ZhangLS.Spec.lemma61_error_regular_path_rectangle_cauchy
#print axioms ZhangLS.Spec.lemma61_actual_error_line_shift
#print axioms ZhangLS.Spec.lemma61_short_polynomial_norm_bound
#print axioms ZhangLS.Spec.lemma61_model_Z_P4_factor
#print axioms ZhangLS.Spec.lemma61_actual_Z_original_norm_bound
#print axioms ZhangLS.Spec.lemma61_actual_horizontal_Z_error_factor_bound
#print axioms ZhangLS.Spec.lemma61_actual_horizontal_Z_error_point_bound
#print axioms ZhangLS.Spec.lemma61_actual_horizontal_Z_error_integral_bound
#print axioms ZhangLS.Spec.lemma61_E1_exponential_floor
#print axioms ZhangLS.Spec.lemma61_actual_original_left_Z_error_bound
