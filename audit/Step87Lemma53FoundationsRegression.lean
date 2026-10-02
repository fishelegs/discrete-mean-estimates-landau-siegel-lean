import ZhangLS.Spec.Lemma53

/-! Regression for the actual defining object and completed foundations.
This file does not claim a proof of the still-open Lemma53Target.
-/

open Complex MeasureTheory ZhangLS.Spec

set_option maxHeartbeats 1000000

-- Delta is the original inverse Mellin integral, not the oscillatory proxy.
example (D : ℕ) (x : ℝ) : lemma53PaperDelta D x =
    mellinInv (3 / 2)
      (fun s : ℂ => (((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s *
        Complex.exp ((2 * Real.pi : ℂ) * I * (-s / 4))) *
        (((Real.sqrt Real.pi / (Real.log D) ^ 400 : ℝ) : ℂ) *
          Complex.exp ((s - (lemma23PaperCenter D)) ^ 2 /
            (4 * (((Real.log D) ^ 400 : ℝ) : ℂ) ^ 2)))) x *
      Complex.exp ((2 * Real.pi : ℂ) * I * (x : ℂ)) := by
  rfl

example {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-((3 / 2 : ℂ) + (t : ℂ) * I)) *
      (lemma53PaperThetaStar ((3 / 2 : ℂ) + (t : ℂ) * I) *
        lemma53PaperOmega D ((3 / 2 : ℂ) + (t : ℂ) * I))) :=
  lemma53_defining_mellin_integrable hD hx

-- The Gaussian main term has exactly the original scale L^400.
example {D : ℕ} (hD : 1 < D) (x : ℝ) :
    (∫ u : ℝ, Complex.exp ((2 * Real.pi : ℂ) * I *
      (((Real.log D) ^ 519 - x : ℝ) : ℂ) * (u : ℂ) -
        (((Real.log D) ^ 400 : ℝ) : ℂ) ^ 2 * (u : ℂ) ^ 2)) =
      ((Real.sqrt Real.pi / (Real.log D) ^ 400 *
        Real.exp (-((Real.pi * (x - (Real.log D) ^ 519) / (Real.log D) ^ 400) ^ 2)) : ℝ) : ℂ) := by
  exact (lemma53_gaussian_main_term hD x).trans (lemma53_omega_critical_gaussian D x)

example {D : ℕ} (hD : 1 < D) (x : ℝ) :
    Integrable (fun u : ℝ => lemma53OscillatoryKernel D x (u : ℂ)) :=
  lemma53_oscillatory_kernel_integrable hD x

-- The shifted formula is valid at v=0 as well as on both shifted paths.
example (D : ℕ) (x u : ℝ) :
    ‖lemma53OscillatoryKernel D x ((u : ℂ) + (0 : ℂ) * I)‖ =
      Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) := by
  simpa using lemma53_oscillatory_kernel_norm_shifted D x u 0

-- The perturbation is exactly one at the origin.
example (x : ℝ) : lemma53Perturbation x 0 = 1 := by
  simp [lemma53Perturbation]

#print axioms lemma53_gaussian_laplace
#print axioms lemma53_gaussian_main_term
#print axioms lemma53_omega_critical_gaussian
#print axioms lemma53_omega_critical_pos
#print axioms lemma53_kernel_factorization
#print axioms lemma53_defining_mellin_integrable
#print axioms lemma53_oscillatory_kernel_integrable
#print axioms lemma53_oscillatory_delta_norm_bound
#print axioms lemma53_perturbation_sub_one_bound
#print axioms lemma53_oscillatory_kernel_norm_shifted
#print axioms lemma53_gaussian_phase_norm_at_stationary_line
