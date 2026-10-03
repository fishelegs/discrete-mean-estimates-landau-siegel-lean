import ZhangLS.Spec.Lemma162CorrectedQuantitative
import ZhangLS.Spec.Lemma57ContourAnalyticity
import ZhangLS.Spec.Lemma56

/-! Actual regularized numerator for the repaired Section 16 integrand.
The original T, both finite shifts, the actual Euler product, the entire
Dirichlet L function and the source Gaussian are retained. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 1500000

/-- Exactly T^w ω₁(w), with T = exp((log D)^(11/10)). -/
noncomputable def lemma162MellinSmoothing (D : ℕ) (w : ℂ) : ℂ :=
  Complex.exp ((Real.log (lemma56PaperT D) : ℂ)*w +
    w^2/(4*(Real.log (D : ℝ) : ℂ)^30))

theorem lemma162_mellin_smoothing_source (D : ℕ) (w : ℂ) :
    lemma162MellinSmoothing D w = (lemma56PaperT D : ℂ)^w*lemma57OmegaOne D w := by
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hT.ne')]
  rw [← Complex.ofReal_log hT.le]
  simp only [lemma162MellinSmoothing, lemma57OmegaOne, Complex.exp_add]

theorem lemma162_mellin_smoothing_differentiable (D : ℕ) :
    Differentiable ℂ (lemma162MellinSmoothing D) := by
  unfold lemma162MellinSmoothing
  fun_prop

@[simp] theorem lemma162_mellin_smoothing_zero (D : ℕ) :
    lemma162MellinSmoothing D 0 = 1 := by
  simp [lemma162MellinSmoothing]

/-- Exact smoothing norm; its real-axis growth must be included in a disk
bound. In particular T^w is not uniformly bounded on the 1/(10 log D) disk. -/
theorem lemma162_mellin_smoothing_norm (D : ℕ) (w : ℂ) :
    ‖lemma162MellinSmoothing D w‖ =
      Real.exp (Real.log (lemma56PaperT D)*w.re+
        (w.re^2-w.im^2)/(4*Real.log (D : ℝ)^30)) := by
  rw [lemma162MellinSmoothing,Complex.norm_exp,Complex.add_re]
  have hcast : (4*(Real.log (D : ℝ) : ℂ)^30) = ((4*Real.log (D : ℝ)^30 : ℝ) : ℂ) := by
    norm_cast
  rw [hcast,Complex.div_ofReal_re,pow_two,Complex.mul_re,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  congr 1
  ring

theorem lemma162_mellin_smoothing_disk_bound {D : ℕ} (hD : 1<D)
    {R : ℝ} (hR : 0≤R) {w : ℂ} (hw : ‖w‖≤R) :
    ‖lemma162MellinSmoothing D w‖≤
      Real.exp (Real.log (lemma56PaperT D)*R+R^2/(4*Real.log (D : ℝ)^30)) := by
  have hL : 0<Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast hD)
  have hT : 0≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    exact Real.rpow_nonneg (by simpa [lemma23PaperL] using hL.le) _
  have hsq : w.re^2-w.im^2≤R^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg w.re) hR).mpr ((Complex.abs_re_le_norm w).trans hw)
    rw [sq_abs] at hh
    nlinarith [sq_nonneg w.im]
  rw [lemma162_mellin_smoothing_norm]
  apply Real.exp_le_exp.mpr
  exact add_le_add (mul_le_mul_of_nonneg_left ((Complex.re_le_norm w).trans hw) hT)
    (div_le_div_of_nonneg_right hsq (by positivity))

/-- The genuine shifted zeta/L/V integrand, including the ds/w factor. -/
noncomputable def lemma162MellinIntegrand {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ w : ℂ) : ℂ :=
  lemma162CorrectedEulerProduct χ β γ (1+w)*riemannZeta (1+w)^2*
    riemannZeta (1+w-γ)*dirichletLFunction χ (1+w)*
      dirichletLFunction χ (1+w-γ)^2*lemma162MellinSmoothing D w/w

/-- H(w); the regularized zeta values are the analytic values, including Z(0)=1. -/
noncomputable def lemma162MellinNumerator {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ w : ℂ) : ℂ :=
  lemma162CorrectedEulerProduct χ β γ (1+w)*lemma57RegularizedZeta w^2*
    lemma57RegularizedZeta (w-γ)*dirichletLFunction χ (1+w)*
      dirichletLFunction χ (1+w-γ)^2*lemma162MellinSmoothing D w

theorem lemma162_mellin_pole_removal {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) {w : ℂ} (hw : w≠0) (hγ : w≠γ) :
    lemma162MellinIntegrand χ β γ w = lemma162MellinNumerator χ β γ w/(w^3*(w-γ)) := by
  have hwγ : w-γ≠0 := sub_ne_zero.mpr hγ
  simp only [lemma162MellinIntegrand,lemma162MellinNumerator,
    lemma57RegularizedZeta,if_neg hw,if_neg hwγ]
  rw [show 1+(w-γ)=1+w-γ by ring]
  field_simp

/-- Identification with the actual convergent arithmetic Dirichlet series.
This theorem is pointwise on Re(w)>0; it does not assert Mellin inversion. -/
theorem lemma162_mellin_actual_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0)
    (hstar : lemma161Star χ β (1-γ)≠0) (w : ℂ) (hw : 0<w.re) :
    lemma162MellinIntegrand χ β γ w =
      lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) (1+w)*
        (lemma56PaperT D : ℂ)^w*lemma57OmegaOne D w/w := by
  have hh := lemma162_actual_shifted_euler_identity χ β hβ γ hγ hstar (1+w)
    (by simpa using hw)
  rw [lemma162MellinIntegrand,lemma162_mellin_smoothing_source]
  rw [← hh]
  unfold lemma162ShiftedMainFactor
  ring

theorem lemma162_mellin_numerator_analytic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) :
    AnalyticOnNhd ℂ (lemma162MellinNumerator χ β γ) {w : ℂ | -(1/10)<w.re} := by
  intro w hw
  change -(1/10)<w.re at hw
  have hvdomain : 9/10<(1+w).re := by
    rw [Complex.add_re,Complex.one_re]
    linarith
  have hV : AnalyticAt ℂ (fun w => lemma162CorrectedEulerProduct χ β γ (1+w)) w :=
    (lemma162_corrected_euler_analytic χ β hβ γ hγ (1+w) hvdomain).comp
        (f := fun z : ℂ => 1+z)
        (by fun_prop)
  have hZ := lemma57RegularizedZeta_differentiable.analyticAt w
  have hZγ : AnalyticAt ℂ (fun w => lemma57RegularizedZeta (w-γ)) w :=
    (lemma57RegularizedZeta_differentiable.analyticAt (w-γ)).comp
      (f := fun z : ℂ => z-γ) (by fun_prop)
  have hL : AnalyticAt ℂ (fun w => dirichletLFunction χ (1+w)) w :=
    ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD).analyticAt (1+w)).comp
      (f := fun z : ℂ => 1+z) (by fun_prop)
  have hLγ : AnalyticAt ℂ (fun w => dirichletLFunction χ (1+w-γ)) w :=
    ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD).analyticAt (1+w-γ)).comp
      (f := fun z : ℂ => 1+z-γ) (by fun_prop)
  exact (((((hV.mul (hZ.pow 2)).mul hZγ).mul hL).mul (hLγ.pow 2)).mul
    ((lemma162_mellin_smoothing_differentiable D).analyticAt w))

@[simp] theorem lemma162_mellin_numerator_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) :
    lemma162MellinNumerator χ β γ 0 = lemma162CorrectedEulerProduct χ β γ 1*
      lemma57RegularizedZeta (-γ)*dirichletLFunction χ 1*dirichletLFunction χ (1-γ)^2 := by
  simp [lemma162MellinNumerator]

@[simp] theorem lemma162_mellin_numerator_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) :
    lemma162MellinNumerator χ β γ γ = lemma162CorrectedEulerProduct χ β γ (1+γ)*
      lemma57RegularizedZeta γ^2*dirichletLFunction χ (1+γ)*dirichletLFunction χ 1^2*
        lemma162MellinSmoothing D γ := by
  simp [lemma162MellinNumerator]

end ZhangLS.Spec
