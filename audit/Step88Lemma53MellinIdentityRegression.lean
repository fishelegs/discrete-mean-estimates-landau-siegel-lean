import ZhangLS.Spec.Lemma53

/-! Regression for the original inverse Mellin object and its proved
oscillatory representation. The original two-range target stays open. -/

open Complex MeasureTheory ZhangLS.Spec

set_option maxHeartbeats 1000000

-- Inverse Mellin inversion holds on every real line for the actual weight.
example {D : ℕ} (hD : 1 < D) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (lemma53PaperOmega D) x =
      Complex.exp (-lemma23PaperCenter D * (Real.log x : ℂ) -
        (lemma53PaperScale D : ℂ) ^ 2 * (Real.log x : ℂ) ^ 2) :=
  lemma53_omega_inverse hD σ hx

-- The Gamma integral is proved for a complex, not only a real, decay.
example {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (s - 1) * Complex.exp (-z * (y : ℂ))) =
      z ^ (-s) * Complex.Gamma s :=
  lemma53_gamma_laplace hs hz

-- The product-measure convergence needed for Fubini is a proved result.
example {D : ℕ} (hD : 1 < D) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun p : ℝ × ℝ => lemma53GammaGaussianKernel D z p.1 p.2)
      (volume.prod (volume.restrict (Set.Ioi 0))) :=
  lemma53_gamma_gaussian_product_integrable hD hz

-- The exact oscillatory formula uses the paper's actual Mellin definition.
example {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    mellinInv (3 / 2) (fun s => lemma53PaperThetaStar s * lemma53PaperOmega D s) x *
      Complex.exp ((2 * Real.pi : ℂ) * I * (x : ℂ)) =
      ∫ u : ℝ, Complex.exp (lemma23PaperCenter D * (u : ℂ) -
        (((Real.log D) ^ 400 : ℝ) : ℂ) ^ 2 * (u : ℂ) ^ 2 -
          (2 * Real.pi : ℂ) * I * (x : ℂ) * (Complex.exp (u : ℂ) - 1)) := by
  exact lemma53_mellin_oscillatory_identity hD hx

example {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    lemma53PaperDeltaOne D x =
      ∫ y : ℝ in Set.Ioi 0, Complex.exp ((lemma23PaperCenter D - 1) * (Real.log y : ℂ) -
        (lemma53PaperScale D : ℂ) ^ 2 * (Real.log y : ℂ) ^ 2 -
          (2 * Real.pi : ℂ) * I * (x : ℂ) * (y : ℂ)) :=
  lemma53_delta_one_log_gaussian hD hx

-- Inversion normalization at x=1 is exactly one, independently of the line.
example {D : ℕ} (hD : 1 < D) (σ : ℝ) :
    mellinInv σ (lemma53PaperOmega D) 1 = 1 := by
  simpa using lemma53_omega_inverse hD σ zero_lt_one

#print axioms lemma53_gaussian_inverse
#print axioms lemma53_gamma_laplace_integrable
#print axioms lemma53_gamma_laplace_differentiableAt
#print axioms lemma53_gamma_laplace
#print axioms lemma53_gamma_gaussian_product_integrable
#print axioms lemma53_regularized_mellin
#print axioms lemma53_exp_change_of_variables
#print axioms lemma53_mellin_boundary_limit
#print axioms lemma53_exponential_boundary_limit
#print axioms lemma53_boundary_gamma_factor
#print axioms lemma53_delta_one_log_gaussian
#print axioms lemma53_mellin_oscillatory_identity
#print axioms lemma53_paper_delta_norm_bound
