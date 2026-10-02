import ZhangLS.Spec.Lemma171AnalyticCorrection
import ZhangLS.Spec.Lemma32RegularNumerator
import ZhangLS.Spec.Lemma56
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Lemma 17.1: actual Gaussian integrand and third-order-pole residue

The numerator uses the genuine pole-removed zeta, genuine L-function and the
analytic correction already identified with the actual ν² Dirichlet series.
The smoothing scale is the paper's T=exp((log D)^(11/10)), not D⁴ or P.
The residue is identified by the Cauchy integral formula. Its uniform difference
from a, the actual left-line shift, and unsmoothing are proved in the subsequent
`Lemma171ResidueBound`, `Lemma171ContourInfinite`, and Gaussian modules.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Metric Set
open scoped Classical
set_option maxHeartbeats 2000000

/-- The entire factor T^w ω₁(w), expressed without a logarithm branch. -/
noncomputable def lemma171GaussianMellinFactor (D : ℕ) (w : ℂ) : ℂ :=
  Complex.exp (((lemma23PaperL D ^ (11/10 : ℝ) : ℝ) : ℂ)*w +
    w^2/(4*(Real.log (D : ℝ) : ℂ)^30))

lemma lemma171_gaussian_factor_eq_paper (D : ℕ) (w : ℂ) :
    lemma171GaussianMellinFactor D w =
      (lemma56PaperT D : ℂ)^w * lemma57OmegaOne D w := by
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  unfold lemma171GaussianMellinFactor lemma57OmegaOne
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hT.ne'),
    ← Complex.ofReal_log hT.le,lemma56PaperT,Real.log_exp,← Complex.exp_add]

lemma lemma171_gaussian_factor_differentiable (D : ℕ) :
    Differentiable ℂ (lemma171GaussianMellinFactor D) := by
  unfold lemma171GaussianMellinFactor
  fun_prop

lemma lemma171_gaussian_factor_zero (D : ℕ) : lemma171GaussianMellinFactor D 0 = 1 := by
  simp [lemma171GaussianMellinFactor]

/-- The exact integrand displayed in Appendix B after the Euler identity. -/
noncomputable def lemma171MellinIntegrand {D : ℕ} (χ : RealPrimitiveCharacter D) (w : ℂ) : ℂ :=
  lemma171AnalyticCorrection D (1+w) *
    (riemannZeta (1+w)*dirichletLFunction χ (1+w))^2 *
    lemma171GaussianMellinFactor D w / w

lemma lemma171_mellin_integrand_eq_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    (w : ℂ) (hw : 0 < w.re) :
    lemma171MellinIntegrand χ w =
      lemma171DirichletSeries χ (1+w) *
        ((lemma56PaperT D : ℂ)^w * lemma57OmegaOne D w) / w := by
  have hr : 1 < (1+w).re := by simp; exact hw
  rw [lemma171_dirichlet_series_identity χ (1+w) hr,
    ← lemma171_gaussian_factor_eq_paper]
  rfl

/-- Removing the full cubic pole yields a holomorphic numerator. -/
noncomputable def lemma171RegularNumerator {D : ℕ} (χ : RealPrimitiveCharacter D) (w : ℂ) : ℂ :=
  lemma171AnalyticCorrection D (1+w) *
    (zetaPoleRemoved (1+w)*dirichletLFunction χ (1+w))^2 *
    lemma171GaussianMellinFactor D w

lemma lemma171_regular_numerator_differentiableAt {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (w : ℂ) (hw : -1/2 < w.re) :
    DifferentiableAt ℂ (lemma171RegularNumerator χ) w := by
  have hre : 1/2 < (1+w).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have had : DifferentiableAt ℂ (fun w : ℂ => 1+w) w := by fun_prop
  have hc := ((lemma171_correction_analyticOnNhd D) (1+w) hre).differentiableAt.comp w had
  have hz := (lemma32_zeta_pole_removed_differentiableAt (by linarith : 0 < (1+w).re)).comp w had
  have hl := (differentiable_dirichletLFunction_of_one_lt_modulus χ hD (1+w)).comp w had
  exact (hc.mul ((hz.mul hl).pow 2)).mul (lemma171_gaussian_factor_differentiable D w)

lemma lemma171_regular_numerator_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    AnalyticOnNhd ℂ (lemma171RegularNumerator χ) {w : ℂ | -1/2 < w.re} := by
  exact (show DifferentiableOn ℂ (lemma171RegularNumerator χ) {w : ℂ | -1/2 < w.re} from
    fun w hw => (lemma171_regular_numerator_differentiableAt χ hD w hw).differentiableWithinAt).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

lemma lemma171_regular_numerator_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (w : ℂ) (hw : -1/2 < w.re) (h0 : w ≠ 0) :
    lemma171RegularNumerator χ w = w^3*lemma171MellinIntegrand χ w := by
  have hs0 : 1+w ≠ 0 := by
    intro h; have ht := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at ht; linarith
  have hs1 : 1+w ≠ 1 := by intro h; exact h0 (by linear_combination h)
  have hz := zetaPoleRemoved_eq_mul_riemannZeta hs0 hs1
  unfold lemma171RegularNumerator lemma171MellinIntegrand
  rw [hz]
  simp only [add_sub_cancel_left]
  field_simp

/-- The actual residue of the paper's integrand, not a presumed approximation to a. -/
noncomputable def lemma171ActualResidue {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  iteratedDeriv 2 (lemma171RegularNumerator χ) 0 / (Nat.factorial 2 : ℂ)

lemma lemma171_actual_circle_integral_eq_residue {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (r : ℝ) (hr : 0 < r) (hsmall : r ≤ 1/4) :
    (2*Real.pi*Complex.I : ℂ)⁻¹*circleIntegral (lemma171MellinIntegrand χ) 0 r =
      lemma171ActualResidue χ := by
  have hd : DifferentiableOn ℂ (lemma171RegularNumerator χ) (closedBall 0 r) := by
    intro w hw
    have hn : ‖w‖ ≤ r := by simpa [mem_closedBall,dist_eq_norm] using hw
    have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans (hn.trans hsmall))).1
    exact (lemma171_regular_numerator_differentiableAt χ hD w (by linarith)).differentiableWithinAt
  have hc : circleIntegral (fun w : ℂ => 1/w^3*lemma171RegularNumerator χ w) 0 r =
      ((2*Real.pi*Complex.I : ℂ)/(Nat.factorial 2 : ℂ))*
        iteratedDeriv 2 (lemma171RegularNumerator χ) 0 := by
    simpa only [sub_zero,smul_eq_mul,Nat.reduceAdd] using
      hd.circleIntegral_one_div_sub_center_pow_smul hr 2
  have he : circleIntegral (lemma171MellinIntegrand χ) 0 r =
      circleIntegral (fun w : ℂ => 1/w^3*lemma171RegularNumerator χ w) 0 r := by
    apply circleIntegral.integral_congr hr.le
    intro w hw
    have hn : ‖w‖ = r := by simpa [mem_sphere,dist_eq_norm] using hw
    have h0 : w ≠ 0 := by intro h; rw [h,norm_zero] at hn; linarith
    have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans (hn.le.trans hsmall))).1
    change lemma171MellinIntegrand χ w = 1/w^3*lemma171RegularNumerator χ w
    rw [lemma171_regular_numerator_eq χ w (by linarith) h0]
    field_simp
  rw [he,hc]
  unfold lemma171ActualResidue
  field_simp [Complex.two_pi_I_ne_zero]


lemma lemma171_second_deriv_mul (f g : ℂ → ℂ) (x : ℂ)
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    iteratedDeriv 2 (fun z => f z*g z) x =
      f x*iteratedDeriv 2 g x + 2*deriv f x*deriv g x + iteratedDeriv 2 f x*g x := by
  have hh := iteratedDeriv_fun_mul (n := 2) (x := x) hf.contDiffAt hg.contDiffAt
  simpa [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one,Nat.choose,
    mul_assoc,add_assoc] using hh

lemma lemma171_second_deriv_mul_square (f g : ℂ → ℂ) (x : ℂ)
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    iteratedDeriv 2 (fun z => f z*g z^2) x/2 =
      f x*(deriv g x)^2 + g x*(f x*iteratedDeriv 2 g x +
        2*deriv f x*deriv g x + iteratedDeriv 2 f x*g x/2) := by
  have hsq : iteratedDeriv 2 (fun z => g z^2) x =
      g x*iteratedDeriv 2 g x + 2*deriv g x*deriv g x + iteratedDeriv 2 g x*g x := by
    simpa only [pow_two] using lemma171_second_deriv_mul g g x hg hg
  rw [lemma171_second_deriv_mul f (fun z => g z^2) x hf (hg.pow 2),hsq,
    deriv_fun_pow hg.differentiableAt]
  norm_num
  ring

/-- All regular factors other than L(1+w,χ)². -/
noncomputable def lemma171ResiduePrefactor (D : ℕ) (w : ℂ) : ℂ :=
  lemma171AnalyticCorrection D (1+w) * zetaPoleRemoved (1+w)^2 *
    lemma171GaussianMellinFactor D w

lemma lemma171_residue_prefactor_analyticAt (D : ℕ) :
    AnalyticAt ℂ (lemma171ResiduePrefactor D) 0 := by
  have ha : AnalyticAt ℂ (fun w : ℂ => 1+w) 0 := by fun_prop
  have hc := (lemma171_correction_analyticOnNhd D 1 (by norm_num)).comp_of_eq ha (by simp)
  have hz : AnalyticAt ℂ (fun w : ℂ => zetaPoleRemoved (1+w)) 0 :=
    (lemma55_actual_zeta_pole_removed_analyticAt (by norm_num : 0 < (1 : ℂ).re)).comp_of_eq ha (by simp)
  exact (hc.mul (hz.pow 2)).mul ((lemma171_gaussian_factor_differentiable D).analyticAt 0)

lemma lemma171_residue_prefactor_zero (D : ℕ) :
    lemma171ResiduePrefactor D 0 = lemma171AnalyticCorrection D 1 := by
  simp [lemma171ResiduePrefactor,lemma171_gaussian_factor_zero,
    lemma55_actual_zeta_pole_removed_at_one]

lemma lemma171_regular_numerator_factorization {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma171RegularNumerator χ = fun w : ℂ =>
      lemma171ResiduePrefactor D w * dirichletLFunction χ (1+w)^2 := by
  funext w
  unfold lemma171RegularNumerator lemma171ResiduePrefactor
  ring

/-- Exact residue decomposition. Every error term contains the actual small L(1,χ),
so the principal term is precisely a; no bound on the other factors is assumed. -/
lemma lemma171_actual_residue_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    lemma171ActualResidue χ = (lemma171MainTerm χ : ℂ) + LAtOne χ *
      (lemma171AnalyticCorrection D 1 * iteratedDeriv 2 (dirichletLFunction χ) 1 +
        2*deriv (lemma171ResiduePrefactor D) 0*LDerivAtOne χ +
        iteratedDeriv 2 (lemma171ResiduePrefactor D) 0*LAtOne χ/2) := by
  have ha : AnalyticAt ℂ (fun w : ℂ => 1+w) 0 := by fun_prop
  have hl : AnalyticAt ℂ (fun w : ℂ => dirichletLFunction χ (1+w)) 0 :=
    ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD).analyticAt 1).comp_of_eq ha (by simp)
  have hh := lemma171_second_deriv_mul_square (lemma171ResiduePrefactor D)
    (fun w : ℂ => dirichletLFunction χ (1+w)) 0 (lemma171_residue_prefactor_analyticAt D) hl
  unfold lemma171ActualResidue
  rw [lemma171_regular_numerator_factorization]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  rw [hh,lemma171_residue_prefactor_zero,deriv_comp_const_add,iteratedDeriv_comp_const_add]
  simp only [add_zero]
  rw [lemma171_main_term_complex χ hD]
  rfl

end ZhangLS.Spec
