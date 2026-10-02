import ZhangLS.Spec.Lemma56GaussianMellinIdentity
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Actual finite Gaussian contour shift in the proved zero-free strip -/

namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56GaussianArithmeticIntegrand {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x : ℝ) (s : ℂ) : ℂ :=
  -(logDeriv (DirichletCharacter.LFunction θ) s) * (x : ℂ) ^ s * lemma56GaussianOmega B s

lemma lemma56_actual_gaussian_integrand_analyticAt {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (B : ℝ) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hne : DirichletCharacter.LFunction θ s ≠ 0) :
    AnalyticAt ℂ (lemma56GaussianArithmeticIntegrand θ B x) s := by
  have hL := lemma56_actual_L_analyticOnNhd θ hθ s (mem_univ s)
  have hLD : AnalyticAt ℂ (logDeriv (DirichletCharacter.LFunction θ)) s := by
    exact hL.deriv.div hL hne
  have hpower : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s := by
    have he : (fun z : ℂ => (x : ℂ) ^ z) = fun z => Complex.exp (Complex.log (x : ℂ) * z) := by
      funext z
      exact Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne') z
    rw [he]
    fun_prop
  have hOmega : AnalyticAt ℂ (lemma56GaussianOmega B) s := by
    unfold lemma56GaussianOmega
    fun_prop
  exact (hLD.neg.mul hpower).mul hOmega

lemma lemma56_actual_gaussian_rectangle_shift {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (B : ℝ) {x a b H : ℝ}
    (hx : 0 < x) (hab : a ≤ b) (hH : 0 ≤ H)
    (hfree : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ H →
      DirichletCharacter.LFunction θ s ≠ 0) :
    I * (∫ t : ℝ in -H..H, lemma56GaussianArithmeticIntegrand θ B x ((b : ℂ) + (t : ℂ) * I)) =
      I * (∫ t : ℝ in -H..H, lemma56GaussianArithmeticIntegrand θ B x ((a : ℂ) + (t : ℂ) * I)) +
        (∫ σ : ℝ in a..b, lemma56GaussianArithmeticIntegrand θ B x ((σ : ℂ) + (H : ℂ) * I)) -
          (∫ σ : ℝ in a..b, lemma56GaussianArithmeticIntegrand θ B x ((σ : ℂ) - (H : ℂ) * I)) := by
  have hd : DifferentiableOn ℂ (lemma56GaussianArithmeticIntegrand θ B x)
      ((uIcc a b) ×ℂ (uIcc (-H) H)) := by
    intro s hs
    have hre : s.re ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using hs.1
    have him : s.im ∈ Icc (-H) H := by
      simpa only [uIcc_of_le (by linarith only [hH] : -H ≤ H)] using hs.2
    exact (lemma56_actual_gaussian_integrand_analyticAt θ hθ B hx
      (hfree s hre.1 hre.2 (abs_le.mpr him))).differentiableAt.differentiableWithinAt
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (lemma56GaussianArithmeticIntegrand θ B x) ((a : ℂ) - (H : ℂ) * I)
    ((b : ℂ) + (H : ℂ) * I) (by simpa using hd)
  simp only [add_re, sub_re, add_im, sub_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add,
    zero_sub, smul_eq_mul] at hc
  have he (σ : ℝ) : (σ : ℂ) + (-H : ℝ) * I = (σ : ℂ) - (H : ℂ) * I := by push_cast; ring
  simp_rw [he] at hc
  linear_combination hc

theorem lemma56_uniform_primitive_gaussian_rectangle_shift :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {B x H : ℝ}, 0 < x → 0 ≤ H → H ≤ Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) →
        let a := 1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))
        I * (∫ t : ℝ in -H..H, lemma56GaussianArithmeticIntegrand θ B x ((2 : ℂ) + (t : ℂ) * I)) =
          I * (∫ t : ℝ in -H..H, lemma56GaussianArithmeticIntegrand θ B x ((a : ℂ) + (t : ℂ) * I)) +
            (∫ σ : ℝ in a..2, lemma56GaussianArithmeticIntegrand θ B x ((σ : ℂ) + (H : ℂ) * I)) -
              (∫ σ : ℝ in a..2, lemma56GaussianArithmeticIntegrand θ B x ((σ : ℂ) - (H : ℂ) * I)) := by
  obtain ⟨Dhigh, hhigh⟩ := lemma56_uniform_primitive_margin_zero_exclusion
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Dhigh Drep, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B x H hx hH hHmax
  have hf := hhigh χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne
  have hL := (hrep D ((le_max_right _ _).trans hDN)).1
  have hs := lemma56_high_scale_strict_margin hL
  have hVp : 0 < (3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ) := lt_of_lt_of_le (by norm_num) hs.2.2.1
  have hInv : 0 < 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)) := by positivity
  apply lemma56_actual_gaussian_rectangle_shift θ
    (lemma56_primitive_positive_level_nonprincipal θ hθ hq1) B hx
    (by linarith only [hInv])
    hH
  intro s hre _hσ2 ht
  apply hf s
  · have he : 2 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)) =
        2 * (1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by ring
    rw [he]
    have hp : 0 < 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)) := by positivity
    linarith only [hre, hp]
  · have he := Real.exp_pos (2 * lemma23PaperL D ^ (9 / 2 : ℝ))
    linarith only [ht, hHmax, he]

end ZhangLS.Spec
