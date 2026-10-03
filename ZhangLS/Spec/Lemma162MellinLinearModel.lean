import ZhangLS.Spec.Lemma162ActualMellinResidues

/-! Exact extraction of the three genuine L factors. This makes visible the
shift correction to the linear L model, before imposing a numerical remainder. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 1000000

noncomputable def lemma162MellinPrefactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ w : ℂ) : ℂ :=
  lemma162CorrectedEulerProduct χ β γ (1+w)*lemma57RegularizedZeta w^2*
    lemma57RegularizedZeta (w-γ)*lemma162MellinSmoothing D w

noncomputable def lemma162MellinLProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ w : ℂ) : ℂ := dirichletLFunction χ (1+w)*dirichletLFunction χ (1+w-γ)^2

theorem lemma162_mellin_extract_L_product {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ w : ℂ) :
    lemma162MellinNumerator χ β γ w =
      lemma162MellinPrefactor χ β γ w*lemma162MellinLProduct χ γ w := by
  unfold lemma162MellinNumerator lemma162MellinPrefactor lemma162MellinLProduct
  ring

theorem lemma162_mellin_prefactor_analytic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    AnalyticOnNhd ℂ (lemma162MellinPrefactor χ β γ) {w : ℂ | -(1/10)<w.re} := by
  intro w hw
  change -(1/10)<w.re at hw
  have hd : 9/10<(1+w).re := by rw [Complex.add_re,Complex.one_re]; linarith
  have hV := (lemma162_corrected_euler_analytic χ β hβ γ hγ (1+w) hd).comp
    (f := fun z : ℂ => 1+z) (by fun_prop)
  have hZ := lemma57RegularizedZeta_differentiable.analyticAt w
  have hZγ := (lemma57RegularizedZeta_differentiable.analyticAt (w-γ)).comp
    (f := fun z : ℂ => z-γ) (by fun_prop)
  exact ((hV.mul (hZ.pow 2)).mul hZγ).mul
    ((lemma162_mellin_smoothing_differentiable D).analyticAt w)

theorem lemma162_mellin_smoothing_deriv_zero (D : ℕ) :
    HasDerivAt (lemma162MellinSmoothing D) (Real.log (lemma56PaperT D) : ℂ) 0 := by
  have haux (a b : ℂ) : HasDerivAt (fun w : ℂ => Complex.exp (a*w+w^2/b)) a 0 := by
    have hh : HasDerivAt (fun w : ℂ => a*w+w^2/b) a 0 := by
      convert ((hasDerivAt_id (0 : ℂ)).const_mul a).add
        (((hasDerivAt_id (0 : ℂ)).pow 2).div_const b) using 1
      simp
    simpa using hh.cexp
  exact haux (Real.log (lemma56PaperT D) : ℂ) (4*(Real.log (D : ℝ) : ℂ)^30)

@[simp] theorem lemma162_mellin_prefactor_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) :
    lemma162MellinPrefactor χ β γ 0 =
      lemma162CorrectedEulerProduct χ β γ 1*lemma57RegularizedZeta (-γ) := by
  simp [lemma162MellinPrefactor]

/-- The exact shift correction retains the actual V′, shifted regularized
zeta derivative, Euler constant, and log T from the Gaussian smoothing. -/
theorem lemma162_mellin_prefactor_deriv_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    deriv (lemma162MellinPrefactor χ β γ) 0 =
      deriv (lemma162CorrectedEulerProduct χ β γ) 1*lemma57RegularizedZeta (-γ)+
      lemma162CorrectedEulerProduct χ β γ 1*deriv lemma57RegularizedZeta (-γ)+
      (2*(Real.eulerMascheroniConstant : ℂ)+(Real.log (lemma56PaperT D) : ℂ))*
        lemma162CorrectedEulerProduct χ β γ 1*lemma57RegularizedZeta (-γ) := by
  have hV : HasDerivAt (fun w => lemma162CorrectedEulerProduct χ β γ (1+w))
      (deriv (lemma162CorrectedEulerProduct χ β γ) 1) 0 := by
    have hv := (lemma162_corrected_euler_analytic χ β hβ γ hγ 1 (by norm_num)).differentiableAt.hasDerivAt
    have hv' : HasDerivAt (lemma162CorrectedEulerProduct χ β γ)
        (deriv (lemma162CorrectedEulerProduct χ β γ) 1) (1+(0 : ℂ)) := by simpa using hv
    have hh : HasDerivAt (fun w : ℂ => 1+w) 1 0 := by simpa using (hasDerivAt_id (0 : ℂ)).const_add 1
    simpa only [Function.comp_def,mul_one] using hv'.comp 0 hh
  have hZγ : HasDerivAt (fun w => lemma57RegularizedZeta (w-γ))
      (deriv lemma57RegularizedZeta (-γ)) 0 := by
    have hz := (lemma57RegularizedZeta_differentiable (-γ)).hasDerivAt
    have hz' : HasDerivAt lemma57RegularizedZeta (deriv lemma57RegularizedZeta (-γ))
        ((0 : ℂ)-γ) := by simpa using hz
    simpa only [Function.comp_def,mul_one] using hz'.comp 0 ((hasDerivAt_id (0 : ℂ)).sub_const γ)
  have hh := (((hV.mul (lemma57RegularizedZeta_hasDerivAt_zero.pow 2)).mul hZγ).mul
    (lemma162_mellin_smoothing_deriv_zero D)).deriv
  convert hh using 1
  simp [Pi.mul_apply,Pi.pow_apply]
  ring

/-- Exact integral of the source linear L model on a circle enclosing both
points. Its residue is K(A(0)−gamma A′(0)), not just K A(0). -/
theorem lemma162_linear_L_model_circle (A : ℂ → ℂ) (K : ℂ) {γ : ℂ} {R : ℝ}
    (hγR : ‖γ‖<R) (hA : DifferentiableOn ℂ A (closedBall 0 R)) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral
      (fun w => A w*(K*w*(w-γ)^2)/(w^3*(w-γ))) 0 R =
        K*(A 0-γ*deriv A 0) := by
  have hR : 0<R := (norm_nonneg _).trans_lt hγR
  have h0 : (0 : ℂ)∉sphere 0 R := by simpa using ne_of_lt hR
  have hγs : γ∉sphere 0 R := by simpa [mem_sphere] using ne_of_lt hγR
  have hcont := hA.continuousOn.mono sphere_subset_closedBall
  have h1 := lemma162_cauchy_pole_integrable A hR hcont h0 1
  have h2 := lemma162_cauchy_pole_integrable A hR hcont h0 2
  simp only [sub_zero,pow_one] at h1 h2
  have hK : CircleIntegrable (fun w => K*(A w/w)) 0 R := h1.const_mul K
  have hKg : CircleIntegrable (fun w => (K*γ)*(A w/w^2)) 0 R := h2.const_mul (K*γ)
  have he : circleIntegral (fun w => A w*(K*w*(w-γ)^2)/(w^3*(w-γ))) 0 R =
      circleIntegral (fun w => K*(A w/w)-(K*γ)*(A w/w^2)) 0 R := by
    apply circleIntegral.integral_congr hR.le
    intro w hw
    have hw0 : w≠0 := by intro h; subst w; exact h0 hw
    have hwγ : w-γ≠0 := sub_ne_zero.mpr (by intro h; subst w; exact hγs hw)
    field_simp
  rw [he,circleIntegral.integral_sub hK hKg]
  simp only [circleIntegral.integral_const_mul]
  have hc1 := lemma162_cauchy_center A hR hA 0
  have hc2 := lemma162_cauchy_center A hR hA 1
  simp only [sub_zero,Nat.reduceAdd,pow_one,iteratedDeriv_zero,iteratedDeriv_one,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one] at hc1 hc2
  calc
    _ = K*((2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => A w/w) 0 R)-
      K*γ*((2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => A w/w^2) 0 R) := by ring
    _ = _ := by rw [hc1,hc2]; ring

/-- Exact actual three-L-factor error, before any use of Assumption (A). -/
theorem lemma162_actual_L_product_error_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ w : ℂ) :
    lemma162MellinLProduct χ γ w-LDerivAtOne χ^3*w*(w-γ)^2 =
      (dirichletLFunction χ (1+w)-LDerivAtOne χ*w)*dirichletLFunction χ (1+w-γ)^2+
        (LDerivAtOne χ*w)*(dirichletLFunction χ (1+w-γ)-LDerivAtOne χ*(w-γ))*
          (dirichletLFunction χ (1+w-γ)+LDerivAtOne χ*(w-γ)) := by
  unfold lemma162MellinLProduct
  ring

/-- The preceding evaluated circle is used by the actual Section 16 factors,
with the genuine finite shift and the actual derivative L′(1,χ). -/
theorem lemma162_actual_linear_L_model_circle {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) {R : ℝ}
    (hγR : ‖γ‖<R) (hRsmall : R<1/10) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral
      (fun w => lemma162MellinPrefactor χ β γ w*(LDerivAtOne χ^3*w*(w-γ)^2)/
        (w^3*(w-γ))) 0 R =
      LDerivAtOne χ^3*(lemma162CorrectedEulerProduct χ β γ 1*lemma57RegularizedZeta (-γ)-
        γ*deriv (lemma162MellinPrefactor χ β γ) 0) := by
  have hA : AnalyticOnNhd ℂ (lemma162MellinPrefactor χ β γ) (closedBall 0 R) := by
    intro w hw
    apply lemma162_mellin_prefactor_analytic χ β hβ γ hγ
    have hn : ‖w‖≤R := by simpa using hw
    have hre := (Complex.abs_re_le_norm w).trans hn
    have := (abs_le.mp hre).1
    change -(1/10)<w.re
    linarith
  simpa only [lemma162_mellin_prefactor_zero] using
    lemma162_linear_L_model_circle (lemma162MellinPrefactor χ β γ) (LDerivAtOne χ^3) hγR hA.differentiableOn

/-- Ordinary Taylor-factor bounds propagate with all three factors retained. -/
theorem lemma162_actual_L_product_error_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (γ w : ℂ) {E₀ E₁ A B₀ B₁ : ℝ}
    (hE₀ : 0≤E₀) (hE₁ : 0≤E₁) (hB₀ : 0≤B₀)
    (he₀ : ‖dirichletLFunction χ (1+w)-LDerivAtOne χ*w‖≤E₀)
    (he₁ : ‖dirichletLFunction χ (1+w-γ)-LDerivAtOne χ*(w-γ)‖≤E₁)
    (ha : ‖dirichletLFunction χ (1+w-γ)‖≤A)
    (hb₀ : ‖LDerivAtOne χ*w‖≤B₀) (hb₁ : ‖LDerivAtOne χ*(w-γ)‖≤B₁) :
    ‖lemma162MellinLProduct χ γ w-LDerivAtOne χ^3*w*(w-γ)^2‖≤
      E₀*A^2+B₀*E₁*(A+B₁) := by
  rw [lemma162_actual_L_product_error_identity]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_pow,norm_mul,norm_mul]
  apply add_le_add
  · exact mul_le_mul he₀ (pow_le_pow_left₀ (norm_nonneg _) ha 2) (by positivity) hE₀
  · apply mul_le_mul
    · exact mul_le_mul hb₀ he₁ (norm_nonneg _) hB₀
    · exact (norm_add_le _ _).trans (add_le_add ha hb₁)
    · exact norm_nonneg _
    · exact mul_nonneg hB₀ hE₁

end ZhangLS.Spec
