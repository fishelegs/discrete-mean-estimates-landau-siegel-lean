import ZhangLS.Spec.Lemma57MellinContour
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The scalar Gaussian inverse-Mellin kernel in Zhang's Lemma 5.7

This file isolates the scalar analytic core of the Mellin identity from the
Dirichlet-series interchange.  For `s = σ + it`, the paper uses

`x^s * exp (s² / (4 (log D)^30)) / s`.

We prove that this kernel is absolutely integrable on every nonzero vertical
line, identify its normalized vertical integral with mathlib's `mellinInv`, and
reduce its evaluation at `x > 0` to one explicit Mellin-transform formula for
the reciprocal cumulative Gaussian.

Thus no convergence convention is hidden in the remaining transform
obligation `Lemma57GaussianKernelTransform`.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory
open scoped Real

/-- The scalar integrand left after a single Dirichlet-series coefficient is
factored out of Zhang's Mellin integral. -/
noncomputable def lemma57GaussianKernelIntegrand
    (D : ℕ) (σ x t : ℝ) : ℂ :=
  (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) *
    lemma57OmegaOne D ((σ : ℂ) + (t : ℂ) * I) /
      ((σ : ℂ) + (t : ℂ) * I)

/-- Gaussian damping makes the scalar kernel absolutely integrable on every
vertical line not passing through its pole at zero. -/
theorem lemma57GaussianKernel_integrable
    {D : ℕ} (hD : 1 < D) {σ x : ℝ} (hσ : σ ≠ 0) (hx : 0 < x) :
    Integrable (lemma57GaussianKernelIntegrand D σ x) := by
  let L : ℝ := Real.log (D : ℝ)
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hD)
  let b : ℝ := 1 / (4 * L ^ 30)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hgauss : Integrable (fun t : ℝ => Real.exp (-b * t ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  let C : ℝ := x ^ σ * Real.exp (b * σ ^ 2) / |σ|
  have hmajor : Integrable (fun t : ℝ => C * Real.exp (-b * t ^ 2)) :=
    hgauss.const_mul C
  have hden : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t hzero
    have hre := congrArg Complex.re hzero
    exact hσ (by simpa using hre)
  apply hmajor.mono
  · apply Continuous.aestronglyMeasurable
    unfold lemma57GaussianKernelIntegrand lemma57OmegaOne
    have hscont : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) := by
      fun_prop
    have hpowcont : Continuous (fun t : ℝ =>
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)) :=
      hscont.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    have hexpcont : Continuous (fun t : ℝ =>
        Complex.exp (((σ : ℂ) + (t : ℂ) * I) ^ 2 /
          (4 * (Real.log (D : ℝ) : ℂ) ^ 30))) := by
      fun_prop
    have hnum : Continuous (fun t : ℝ =>
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) *
          Complex.exp (((σ : ℂ) + (t : ℂ) * I) ^ 2 /
            (4 * (Real.log (D : ℝ) : ℂ) ^ 30))) :=
      hpowcont.mul hexpcont
    have hdencont : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) := by
      fun_prop
    exact hnum.div₀ hdencont hden
  · filter_upwards [] with t
    have homega :
        ‖lemma57OmegaOne D ((σ : ℂ) + (t : ℂ) * I)‖ =
          Real.exp ((σ ^ 2 - t ^ 2) / (4 * L ^ 30)) := by
      rw [lemma57OmegaOne, norm_exp]
      congr 1
      have hcast :
          4 * (Real.log (D : ℝ) : ℂ) ^ 30 = (4 * L ^ 30 : ℝ) := by
        dsimp [L]
        push_cast
        ring
      have hsq :
          (((σ : ℂ) + (t : ℂ) * I) ^ 2).re = σ ^ 2 - t ^ 2 := by
        rw [pow_two, Complex.mul_re]
        simp
        ring
      have hinv : ((4 * L ^ 30 : ℝ) : ℂ)⁻¹ =
          ((4 * L ^ 30)⁻¹ : ℝ) := by norm_cast
      rw [hcast, div_eq_mul_inv, hinv, Complex.mul_re, hsq]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      field_simp
    rw [lemma57GaussianKernelIntegrand, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx, homega]
    have hnorm : |σ| ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := by
      calc
        |σ| = |(((σ : ℂ) + (t : ℂ) * I)).re| := by simp
        _ ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := Complex.abs_re_le_norm _
    have hdenpos : 0 < ‖(σ : ℂ) + (t : ℂ) * I‖ :=
      norm_pos_iff.mpr (hden t)
    have habsσ : 0 < |σ| := abs_pos.mpr hσ
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC,
      abs_of_pos (Real.exp_pos _)]
    have hnumpos :
        0 ≤ x ^ σ * Real.exp ((σ ^ 2 - t ^ 2) / (4 * L ^ 30)) := by
      positivity
    have hdiv :
        x ^ σ * Real.exp ((σ ^ 2 - t ^ 2) / (4 * L ^ 30)) /
            ‖(σ : ℂ) + (t : ℂ) * I‖ ≤
          x ^ σ * Real.exp ((σ ^ 2 - t ^ 2) / (4 * L ^ 30)) / |σ| := by
      exact div_le_div_of_nonneg_left hnumpos habsσ hnorm
    refine hdiv.trans_eq ?_
    dsimp [C, b]
    have hexponent :
        (σ ^ 2 - t ^ 2) / (4 * L ^ 30) =
          1 / (4 * L ^ 30) * σ ^ 2 +
            (-(1 / (4 * L ^ 30)) * t ^ 2) := by
      field_simp
      ring
    rw [hexponent, Real.exp_add]
    ring

/-- The normalized scalar vertical integral in the paper's `ds = i dt`
parameterization. -/
noncomputable def lemma57GaussianKernelVerticalIntegral
    (D : ℕ) (σ x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∫ t : ℝ, lemma57GaussianKernelIntegrand D σ x t * I

/-- The paper's scalar vertical integral is exactly mathlib's inverse Mellin
transform, evaluated at the reciprocal argument. -/
theorem lemma57GaussianKernelVerticalIntegral_eq_mellinInv
    (D : ℕ) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    lemma57GaussianKernelVerticalIntegral D σ x =
      mellinInv σ (fun s : ℂ => lemma57OmegaOne D s / s) x⁻¹ := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact ne_of_lt Real.pi_pos
  have hpow : ∀ t : ℝ,
      ((x⁻¹ : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) := by
    intro t
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
      Complex.cpow_neg, inv_inv]
  simp only [lemma57GaussianKernelVerticalIntegral,
    lemma57GaussianKernelIntegrand, mellinInv, smul_eq_mul]
  simp_rw [hpow]
  rw [MeasureTheory.integral_mul_const]
  simp only [Complex.real_smul]
  push_cast
  field_simp

/-- The reciprocal weight is the function whose Mellin transform produces
`ω₁(s) / s` in the right half-plane. -/
noncomputable def lemma57ReciprocalGaussianWeight (D : ℕ) (x : ℝ) : ℂ :=
  (zhangGaussianWeight D x⁻¹ : ℂ)

/-- The reciprocal Gaussian weight is continuous at every positive argument. -/
theorem lemma57ReciprocalGaussianWeight_continuousAt
    (D : ℕ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (lemma57ReciprocalGaussianWeight D) x := by
  have hgauss : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    fun_prop
  have hprimitive : Continuous (fun u : ℝ =>
      ∫ t : ℝ in (0 : ℝ)..u, Real.exp (-(t ^ 2))) :=
    (intervalIntegral.differentiable_integral_of_continuous hgauss).continuous
  have hinv : ContinuousAt (fun y : ℝ => y⁻¹) x :=
    continuousAt_id.inv₀ hx.ne'
  have hlog : ContinuousAt (fun y : ℝ => Real.log y⁻¹) x :=
    hinv.log (inv_ne_zero hx.ne')
  have hendpoint : ContinuousAt (fun y : ℝ =>
      (Real.log (D : ℝ)) ^ 15 * Real.log y⁻¹) x :=
    continuousAt_const.mul hlog
  have hint : ContinuousAt (fun y : ℝ =>
      ∫ t : ℝ in (0 : ℝ)..
        (Real.log (D : ℝ)) ^ 15 * Real.log y⁻¹,
          Real.exp (-(t ^ 2))) x :=
    hprimitive.continuousAt.comp hendpoint
  apply Complex.continuous_ofReal.continuousAt.comp
  exact continuousAt_const.add (continuousAt_const.mul hint)

/-- The transform-side scalar function is vertically integrable away from its
pole; this is the exact hypothesis required by `mellinInv_mellin_eq`. -/
theorem lemma57Omega_div_verticalIntegrable
    {D : ℕ} (hD : 1 < D) {σ : ℝ} (hσ : σ ≠ 0) :
    Complex.VerticalIntegrable (fun s : ℂ => lemma57OmegaOne D s / s) σ := by
  unfold Complex.VerticalIntegrable
  apply (lemma57GaussianKernel_integrable hD hσ
    (show (0 : ℝ) < 1 by norm_num)).congr
  filter_upwards [] with t
  simp [lemma57GaussianKernelIntegrand]

/-- The one scalar transform calculation still needed for Gaussian Mellin
inversion.  It is stated as a `HasMellin`, so convergence and value are both
explicit. -/
def Lemma57GaussianKernelTransform (D : ℕ) : Prop :=
  ∀ s : ℂ, 0 < s.re →
    HasMellin (lemma57ReciprocalGaussianWeight D) s
      (lemma57OmegaOne D s / s)

/-- Once the explicit scalar Mellin transform is known, mathlib's Fourier-based
Mellin inversion theorem evaluates Zhang's scalar kernel at every positive
argument and every positive vertical line. -/
theorem lemma57GaussianKernelVerticalIntegral_eq_weight_of_transform
    {D : ℕ} (hD : 1 < D) (htransform : Lemma57GaussianKernelTransform D)
    {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    lemma57GaussianKernelVerticalIntegral D σ x =
      (zhangGaussianWeight D x : ℂ) := by
  rw [lemma57GaussianKernelVerticalIntegral_eq_mellinInv D σ hx]
  let f := lemma57ReciprocalGaussianWeight D
  have hhas : HasMellin f (σ : ℂ) (lemma57OmegaOne D σ / σ) :=
    htransform σ (by simpa using hσ)
  have hline : ∀ t : ℝ,
      mellin f ((σ : ℂ) + (t : ℂ) * I) =
        lemma57OmegaOne D ((σ : ℂ) + (t : ℂ) * I) /
          ((σ : ℂ) + (t : ℂ) * I) := by
    intro t
    exact (htransform _ (by simpa using hσ)).2
  have hvertical : Complex.VerticalIntegrable (mellin f) σ := by
    apply (lemma57Omega_div_verticalIntegrable hD hσ.ne').congr
    filter_upwards [] with t
    exact (hline t).symm
  have hmellinInv := mellinInv_mellin_eq σ f (inv_pos.mpr hx)
    hhas.1 hvertical
    (lemma57ReciprocalGaussianWeight_continuousAt D (inv_pos.mpr hx))
  calc
    mellinInv σ (fun s : ℂ => lemma57OmegaOne D s / s) x⁻¹ =
        mellinInv σ (mellin f) x⁻¹ := by
      unfold mellinInv
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      rw [hline t]
    _ = f x⁻¹ := hmellinInv
    _ = (zhangGaussianWeight D x : ℂ) := by
      simp [f, lemma57ReciprocalGaussianWeight]

end ZhangLS.Spec
