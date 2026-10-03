import ZhangLS.Spec.Lemma162MellinBudget
import ZhangLS.Spec.Lemma162MellinLinearModel
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric

-- The original T^w omega_1(w), not a substituted smoothing scale.
example (D : ℕ) (w : ℂ) : lemma162MellinSmoothing D w =
    (lemma56PaperT D : ℂ)^w*lemma57OmegaOne D w := lemma162_mellin_smoothing_source D w

-- The actual Gaussian and T growth remain visible.
example (D : ℕ) (w : ℂ) : ‖lemma162MellinSmoothing D w‖ =
    Real.exp (Real.log (lemma56PaperT D)*w.re+(w.re^2-w.im^2)/(4*Real.log (D : ℝ)^30)) :=
  lemma162_mellin_smoothing_norm D w

-- Original beta1: identification with the actual convergent arithmetic series.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ)
    (hM : lemma161Star χ (lemma52PaperBetaOne D c) (1-lemma52PaperBetaOne D c)≠0)
    (w : ℂ) (hw : 0<w.re) :
    lemma162MellinIntegrand χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c) w =
      lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c)
        (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) (1+w)*
        (lemma56PaperT D : ℂ)^w*lemma57OmegaOne D w/w :=
  lemma162_mellin_actual_series χ _ (lemma161_paper_beta_re D c) _ (lemma161_paper_beta_re D c) hM w hw

-- Original beta2: no zero-shift substitution.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ)
    (hM : lemma161Star χ (lemma52PaperBetaOne D c) (1-lemma52PaperBetaTwo D c)≠0)
    (w : ℂ) (hw : 0<w.re) :
    lemma162MellinIntegrand χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c) w =
      lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c)
        (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) (1+w)*
        (lemma56PaperT D : ℂ)^w*lemma57OmegaOne D w/w := by
  apply lemma162_mellin_actual_series χ _ (lemma161_paper_beta_re D c) _ _ hM w hw
  simpa using lemma162_paper_shift_re D c 1

-- The center retains L(1) and the genuine shifted L factor.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β γ : ℂ) :
    lemma162MellinNumerator χ β γ 0 = lemma162CorrectedEulerProduct χ β γ 1*
      lemma57RegularizedZeta (-γ)*dirichletLFunction χ 1*dirichletLFunction χ (1-γ)^2 :=
  lemma162_mellin_numerator_zero χ β γ

-- The beta1 pole retains the two factors L(1)^2.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) :
    lemma162MellinNumerator χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c)
      (lemma52PaperBetaOne D c) =
    lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c)
      (1+lemma52PaperBetaOne D c)*lemma57RegularizedZeta (lemma52PaperBetaOne D c)^2*
      dirichletLFunction χ (1+lemma52PaperBetaOne D c)*dirichletLFunction χ 1^2*
        lemma162MellinSmoothing D (lemma52PaperBetaOne D c) :=
  lemma162_mellin_numerator_shift χ _ _

-- The beta2 pole has the same genuine source factors at its own location.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) :
    lemma162MellinNumerator χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c)
      (lemma52PaperBetaTwo D c) =
    lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c)
      (1+lemma52PaperBetaTwo D c)*lemma57RegularizedZeta (lemma52PaperBetaTwo D c)^2*
      dirichletLFunction χ (1+lemma52PaperBetaTwo D c)*dirichletLFunction χ 1^2*
        lemma162MellinSmoothing D (lemma52PaperBetaTwo D c) :=
  lemma162_mellin_numerator_shift χ _ _

-- Actual enclosing circle for original beta1, including the explicit disk endpoint.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D) (c : ℝ) (hc : 0<c)
    (hL : 3≤lemma23PaperL D) (hs : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral
      (lemma162MellinIntegrand χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c)) 0
      (lemma162MellinRadius D) =
    lemma162ThirdDividedDifference
      (lemma162MellinNumerator χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c))
      (lemma52PaperBetaOne D c) := by
  obtain ⟨h0,_,hsmall,hR,hRsmall⟩ := lemma162_paper_mellin_geometry hc hL hs 0
  simp only [lemma162_paper_shift_zero] at h0 hsmall
  exact (lemma162_actual_residue_sum_circle χ hD _ (lemma161_paper_beta_re D c) _
    (lemma161_paper_beta_re D c) h0 (by linarith) hRsmall).2

-- Actual enclosing circle for original beta2 at the same radius and c'.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D) (c : ℝ) (hc : 0<c)
    (hL : 3≤lemma23PaperL D) (hs : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral
      (lemma162MellinIntegrand χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c)) 0
      (lemma162MellinRadius D) =
    lemma162ThirdDividedDifference
      (lemma162MellinNumerator χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c))
      (lemma52PaperBetaTwo D c) := by
  obtain ⟨h0,_,hsmall,hR,hRsmall⟩ := lemma162_paper_mellin_geometry hc hL hs 1
  simp only [lemma162_paper_shift_one] at h0 hsmall
  have hre : (lemma52PaperBetaTwo D c).re=0 := by simpa using lemma162_paper_shift_re D c 1
  exact (lemma162_actual_residue_sum_circle χ hD _ (lemma161_paper_beta_re D c) _
    hre h0 (by linarith) hRsmall).2

-- The second derivative term is not omitted from the genuine zero residue.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (r : ℝ) (hr : 0<r) (hrγ : r<‖γ‖) (hrs : r<1/10) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (lemma162MellinIntegrand χ β γ) 0 r =
      -iteratedDeriv 2 (lemma162MellinNumerator χ β γ) 0/(2*γ)-
        deriv (lemma162MellinNumerator χ β γ) 0/γ^2-lemma162MellinNumerator χ β γ 0/γ^3 :=
  lemma162_actual_zero_residue χ hD β hβ γ hγ hr hrγ hrs

-- The finite shift correction survives in the actual linear-L model.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re=0)
    (γ : ℂ) (hγ : γ.re=0) (R : ℝ) (hR : ‖γ‖<R) (hrs : R<1/10) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral
      (fun w => lemma162MellinPrefactor χ β γ w*(LDerivAtOne χ^3*w*(w-γ)^2)/(w^3*(w-γ))) 0 R =
      LDerivAtOne χ^3*(lemma162CorrectedEulerProduct χ β γ 1*lemma57RegularizedZeta (-γ)-
        γ*deriv (lemma162MellinPrefactor χ β γ) 0) :=
  lemma162_actual_linear_L_model_circle χ β hβ γ hγ hR hrs

-- The normalized Cauchy remainder keeps every log-D power.
example (L g M : ℝ) (hL : 0<L) (hg : 0≤g) (hM : 0≤M)
    (hs : g<(10*L)⁻¹/2) (hb : g≤3*Real.pi/L^9) :
    M*g/(((10*L)⁻¹)^3*((10*L)⁻¹-g))≤60000*Real.pi*M/L^5 :=
  lemma162_cauchy_log_budget hL hg hM hs hb

end ZhangLS.Spec
