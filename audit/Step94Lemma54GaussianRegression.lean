import ZhangLS.Spec.Lemma54CentralDeltaApproximation
import ZhangLS.Spec.Lemma54

/-! Actual Gaussian, original window and full radius-10-alpha regression.
The entire positive-axis disk normalization and Lemma54Target remain open. -/

open Complex MeasureTheory ZhangLS.Spec Set

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

example {D : ℕ} (hD : 1 < D) :
    Integrable (fun x : ℝ => Real.sqrt Real.pi / (Real.log D) ^ 400 *
      Real.exp (-((Real.pi * (x - (Real.log D) ^ 519) / (Real.log D) ^ 400) ^ 2))) ∧
      (∫ x : ℝ, Real.sqrt Real.pi / (Real.log D) ^ 400 *
        Real.exp (-((Real.pi * (x - (Real.log D) ^ 519) / (Real.log D) ^ 400) ^ 2))) = 1 :=
  lemma54_actual_gaussian_mass hD

example (D : ℕ) (x : ℝ) :
    lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)) =
      (lemma54PaperGaussian D x : ℂ) := lemma54_actual_omega_eq_gaussian D x

example {B W t x : ℝ} (hB : 0 < B) (hW : 0 ≤ W) (hgap : W ≤ |x - t|) :
    lemma54GaussianDensity B t x ≤
      2 * Real.exp (-((Real.pi * W / B) ^ 2) / 2) * lemma54GaussianDensity (2 * B) t x :=
  lemma54_gaussian_exterior_pointwise hB hW hgap

example {D : ℕ} (hL : 2000 ≤ Real.log D) :
    (∫ x : ℝ in (Icc ((Real.log D) ^ 519 - (Real.log D) ^ 405)
      ((Real.log D) ^ 519 + (Real.log D) ^ 405))ᶜ, (1 + x ^ 2) * lemma54PaperGaussian D x) ≤
      144 * (Real.log D) ^ 1838 * Real.exp (-((Real.log D) ^ 10) / 2) :=
  lemma54_actual_gaussian_exterior_quadratic_mass hL (lemma54_window_measurable D).compl
    (fun x hx => lemma54_window_compl_gap D hx)

example {D : ℕ} (hL : 2000 ≤ Real.log D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    1 / 2 ≤ s.re ∧ s.re ≤ 3 / 2 := lemma54_disk_closed_strip hL hs

-- Includes both original closed window endpoints.
example {D : ℕ} (hL : 2000 ≤ Real.log D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) {x : ℝ}
    (hx : (Real.log D) ^ 519 - (Real.log D) ^ 405 ≤ x ∧
      x ≤ (Real.log D) ^ 519 + (Real.log D) ^ 405) :
    ‖(x : ℂ) ^ (s - 1) - 1‖ ≤ 10400 * lemma44PaperAlpha D * Real.log (Real.log D) :=
  lemma54_disk_window_weight_error hL hs hx

-- The actual inverse Mellin Delta, the original window and the original entire disk.
example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖(∫ x : ℝ in Icc ((Real.log D) ^ 519 - (Real.log D) ^ 405)
      ((Real.log D) ^ 519 + (Real.log D) ^ 405),
        (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x) - 1‖ ≤
      10400 * lemma44PaperAlpha D * Real.log (Real.log D) + 3 * lemma44PaperAlpha D +
        (2 + 6 * lemma53SmallErrorConstant * (Real.log D) ^ 405) *
          Real.exp (-((Real.log D) ^ 10) / 2) :=
  lemma54_disk_window_actual_mellin_normalization hD hL hs

#print axioms lemma54_gaussian_density_integrable
#print axioms lemma54_gaussian_density_integral
#print axioms lemma54_actual_omega_eq_gaussian
#print axioms lemma54_actual_gaussian_mass
#print axioms lemma54_gaussian_quadratic_envelope
#print axioms lemma54_gaussian_quadratic_integrable
#print axioms lemma54_gaussian_quadratic_integral_bound
#print axioms lemma54_gaussian_exterior_pointwise
#print axioms lemma54_gaussian_exterior_mass
#print axioms lemma54_gaussian_exterior_quadratic_mass
#print axioms lemma54_window_x_bounds
#print axioms lemma54_window_log_bound
#print axioms lemma54_disk_closed_strip
#print axioms lemma54_disk_window_exponent_budget
#print axioms lemma54_actual_gaussian_exterior_mass
#print axioms lemma54_actual_gaussian_exterior_quadratic_mass
#print axioms lemma54_actual_gaussian_window_mass
#print axioms lemma54_disk_window_weight_error
#print axioms lemma54_disk_window_weighted_error_integrable
#print axioms lemma54_disk_window_weighted_error_integral
#print axioms lemma54_disk_window_gaussian_mellin_normalization
#print axioms lemma54_disk_window_delta_error_integral
#print axioms lemma54_disk_window_actual_mellin_normalization
