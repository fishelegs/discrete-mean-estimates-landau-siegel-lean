import ZhangLS.Spec.Lemma153Repaired
import ZhangLS.Spec.Lemma171Residue

/-! The actual shifted-L Mellin integrand forced by repaired Lemma15.3.
No contour displacement or sharp-cutoff identity is assumed. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 2000000

noncomputable def lemma153MellinIntegrand {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ w : ℂ) : ℂ :=
  lemma153EulerProduct χ β γ (1+w) * riemannZeta (1+w)^2 *
    dirichletLFunction χ (1+w-γ)^2 * lemma171GaussianMellinFactor D w / w

lemma lemma153_mellin_integrand_eq_actual_series {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (hM : lemma152EulerProduct χ β (1-γ) ≠ 0)
    (w : ℂ) (hw : 0<w.re) :
    lemma153MellinIntegrand χ β γ w =
      lemma153DirichletSeries χ β γ (lemma153GeneralMEulerProduct χ β) (1+w) *
        ((lemma56PaperT D : ℂ)^w * lemma57OmegaOne D w) / w := by
  have he := (lemma153_actual_shifted_continuation hD χ β γ hpar hM).2
    (1+w) (by simpa using hw)
  rw [lemma153MellinIntegrand,he.2,lemma171_gaussian_factor_eq_paper]

noncomputable def lemma153ResiduePrefactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ w : ℂ) : ℂ :=
  lemma153EulerProduct χ β γ (1+w) * zetaPoleRemoved (1+w)^2 *
    lemma171GaussianMellinFactor D w

lemma lemma153_residue_prefactor_differentiableAt {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (w : ℂ) (hw : -1/4<w.re) :
    DifferentiableAt ℂ (lemma153ResiduePrefactor χ β γ) w := by
  have hre : 3/4 < (1+w).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have had : DifferentiableAt ℂ (fun w : ℂ => 1+w) w := by fun_prop
  have hu := ((lemma153_euler_product_analyticOnNhd hD χ β γ hpar)
    (1+w) hre).differentiableAt.comp w had
  have hz := (lemma32_zeta_pole_removed_differentiableAt (by linarith : 0 < (1+w).re)).comp w had
  exact (hu.mul (hz.pow 2)).mul (lemma171_gaussian_factor_differentiable D w)

lemma lemma153_residue_prefactor_analyticAt {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) :
    AnalyticAt ℂ (lemma153ResiduePrefactor χ β γ) 0 := by
  have hd : DifferentiableOn ℂ (lemma153ResiduePrefactor χ β γ)
      {w : ℂ | -1/4<w.re} := fun w hw =>
    (lemma153_residue_prefactor_differentiableAt hD χ β γ hpar w hw).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re) 0 (by norm_num)

lemma lemma153_residue_prefactor_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) :
    lemma153ResiduePrefactor χ β γ 0 = lemma153EulerProduct χ β γ 1 := by
  simp [lemma153ResiduePrefactor,lemma171_gaussian_factor_zero,
    lemma55_actual_zeta_pole_removed_at_one]

noncomputable def lemma153RegularNumerator {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ w : ℂ) : ℂ :=
  lemma153ResiduePrefactor χ β γ w * dirichletLFunction χ (1+w-γ)^2

lemma lemma153_regular_numerator_differentiableAt {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (w : ℂ) (hw : -1/4<w.re) :
    DifferentiableAt ℂ (lemma153RegularNumerator χ β γ) w := by
  have had : DifferentiableAt ℂ (fun w : ℂ => 1+w-γ) w := by fun_prop
  have hl := (differentiable_dirichletLFunction_of_one_lt_modulus χ hD (1+w-γ)).comp w had
  exact (lemma153_residue_prefactor_differentiableAt (by omega) χ β γ hpar w hw).mul (hl.pow 2)

lemma lemma153_regular_numerator_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ w : ℂ) (hw : -1/4<w.re) (h0 : w ≠ 0) :
    lemma153RegularNumerator χ β γ w = w^3*lemma153MellinIntegrand χ β γ w := by
  have hs0 : 1+w ≠ 0 := by
    intro h; have ht := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at ht; linarith
  have hs1 : 1+w ≠ 1 := by intro h; exact h0 (by linear_combination h)
  have hz := zetaPoleRemoved_eq_mul_riemannZeta hs0 hs1
  unfold lemma153RegularNumerator lemma153ResiduePrefactor lemma153MellinIntegrand
  rw [hz]
  simp only [add_sub_cancel_left]
  field_simp

/-- Coefficient of w^-1 in the genuine cubic-pole integrand. -/
noncomputable def lemma153ActualResidue {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) : ℂ :=
  iteratedDeriv 2 (lemma153RegularNumerator χ β γ) 0 / (Nat.factorial 2 : ℂ)

lemma lemma153_actual_circle_integral_eq_residue {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (r : ℝ) (hr : 0<r) (hsmall : r≤1/8) :
    (2*Real.pi*Complex.I : ℂ)⁻¹*circleIntegral (lemma153MellinIntegrand χ β γ) 0 r =
      lemma153ActualResidue χ β γ := by
  have hd : DifferentiableOn ℂ (lemma153RegularNumerator χ β γ) (closedBall 0 r) := by
    intro w hw
    have hn : ‖w‖ ≤ r := by simpa [mem_closedBall,dist_eq_norm] using hw
    have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans (hn.trans hsmall))).1
    exact (lemma153_regular_numerator_differentiableAt χ hD β γ hpar w (by linarith)).differentiableWithinAt
  have hc : circleIntegral (fun w : ℂ => 1/w^3*lemma153RegularNumerator χ β γ w) 0 r =
      ((2*Real.pi*Complex.I : ℂ)/(Nat.factorial 2 : ℂ))*
        iteratedDeriv 2 (lemma153RegularNumerator χ β γ) 0 := by
    simpa only [sub_zero,smul_eq_mul,Nat.reduceAdd] using
      hd.circleIntegral_one_div_sub_center_pow_smul hr 2
  have he : circleIntegral (lemma153MellinIntegrand χ β γ) 0 r =
      circleIntegral (fun w : ℂ => 1/w^3*lemma153RegularNumerator χ β γ w) 0 r := by
    apply circleIntegral.integral_congr hr.le
    intro w hw
    have hn : ‖w‖ = r := by simpa [mem_sphere,dist_eq_norm] using hw
    have h0 : w ≠ 0 := by intro h; rw [h,norm_zero] at hn; linarith
    have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans (hn.le.trans hsmall))).1
    change lemma153MellinIntegrand χ β γ w = 1/w^3*lemma153RegularNumerator χ β γ w
    rw [lemma153_regular_numerator_eq χ β γ w (by linarith) h0]
    field_simp
  rw [he,hc]
  unfold lemma153ActualResidue
  field_simp [Complex.two_pi_I_ne_zero]

/-- Exact shifted residue. It does not replace L(1−γ) by −γ L′(1),
and it retains both prefactor derivatives, including U, zeta and Gaussian terms. -/
lemma lemma153_actual_residue_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) :
    lemma153ActualResidue χ β γ =
      lemma153EulerProduct χ β γ 1 * (deriv (dirichletLFunction χ) (1-γ))^2 +
        dirichletLFunction χ (1-γ) *
          (lemma153EulerProduct χ β γ 1 * iteratedDeriv 2 (dirichletLFunction χ) (1-γ) +
            2*deriv (lemma153ResiduePrefactor χ β γ) 0 * deriv (dirichletLFunction χ) (1-γ) +
            iteratedDeriv 2 (lemma153ResiduePrefactor χ β γ) 0 * dirichletLFunction χ (1-γ)/2) := by
  have ha : AnalyticAt ℂ (fun w : ℂ => (1-γ)+w) 0 := by fun_prop
  have hl : AnalyticAt ℂ (fun w : ℂ => dirichletLFunction χ ((1-γ)+w)) 0 :=
    ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD).analyticAt (1-γ)).comp_of_eq ha (by simp)
  have he : lemma153RegularNumerator χ β γ = fun w : ℂ =>
      lemma153ResiduePrefactor χ β γ w * dirichletLFunction χ ((1-γ)+w)^2 := by
    funext w
    simp only [lemma153RegularNumerator]
    rw [show 1+w-γ=(1-γ)+w by ring]
  have hh := lemma171_second_deriv_mul_square (lemma153ResiduePrefactor χ β γ)
    (fun w : ℂ => dirichletLFunction χ ((1-γ)+w)) 0
      (lemma153_residue_prefactor_analyticAt (by omega) χ β γ hpar) hl
  unfold lemma153ActualResidue
  rw [he]
  norm_num only [Nat.factorial,Nat.cast_ofNat]
  rw [hh,lemma153_residue_prefactor_zero,deriv_comp_const_add,iteratedDeriv_comp_const_add]
  simp only [add_zero]

end ZhangLS.Spec
