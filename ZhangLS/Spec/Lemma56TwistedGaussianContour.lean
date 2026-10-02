import ZhangLS.Spec.Lemma56TwistedGaussianMellin

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56TwistedGaussianArithmeticIntegrand {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B x τ : ℝ) (s : ℂ) : ℂ :=
  -(logDeriv (DirichletCharacter.LFunction θ) (s - (τ : ℂ) * I)) *
    (x : ℂ) ^ s * lemma56GaussianOmega B s

lemma lemma56_actual_twisted_gaussian_integrand_analyticAt {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (B τ : ℝ) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hne : DirichletCharacter.LFunction θ (s - (τ : ℂ) * I) ≠ 0) :
    AnalyticAt ℂ (lemma56TwistedGaussianArithmeticIntegrand θ B x τ) s := by
  have hL := lemma56_actual_L_analyticOnNhd θ hθ (s - (τ : ℂ) * I) (Set.mem_univ _)
  have hLD : AnalyticAt ℂ (fun z => logDeriv (DirichletCharacter.LFunction θ)
      (z - (τ : ℂ) * I)) s := by
    have hshift : AnalyticAt ℂ (fun z : ℂ => z - (τ : ℂ) * I) s := by fun_prop
    exact AnalyticAt.comp (f := fun z : ℂ => z - (τ : ℂ) * I) (hL.deriv.div hL hne) hshift
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

lemma lemma56_actual_twisted_gaussian_rectangle_shift {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (B τ : ℝ) {x a b H : ℝ}
    (hx : 0 < x) (hab : a ≤ b) (hH : 0 ≤ H)
    (hfree : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ H →
      DirichletCharacter.LFunction θ (s - (τ : ℂ) * I) ≠ 0) :
    I * (∫ t : ℝ in -H..H,
      lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((b : ℂ) + (t : ℂ) * I)) =
      I * (∫ t : ℝ in -H..H,
        lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((a : ℂ) + (t : ℂ) * I)) +
        (∫ σ : ℝ in a..b,
          lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((σ : ℂ) + (H : ℂ) * I)) -
          (∫ σ : ℝ in a..b,
            lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((σ : ℂ) - (H : ℂ) * I)) := by
  have hd : DifferentiableOn ℂ (lemma56TwistedGaussianArithmeticIntegrand θ B x τ)
      ((Set.uIcc a b) ×ℂ (Set.uIcc (-H) H)) := by
    intro s hs
    have hre : s.re ∈ Set.Icc a b := by
      simpa only [Set.uIcc_of_le hab] using hs.1
    have him : s.im ∈ Set.Icc (-H) H := by
      simpa only [Set.uIcc_of_le (by linarith only [hH] : -H ≤ H)] using hs.2
    exact (lemma56_actual_twisted_gaussian_integrand_analyticAt θ hθ B τ hx
      (hfree s hre.1 hre.2 (abs_le.mpr him))).differentiableAt.differentiableWithinAt
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (lemma56TwistedGaussianArithmeticIntegrand θ B x τ) ((a : ℂ) - (H : ℂ) * I)
    ((b : ℂ) + (H : ℂ) * I) (by simpa using hd)
  simp only [add_re, sub_re, add_im, sub_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add,
    zero_sub, smul_eq_mul] at hc
  have he (σ : ℝ) : (σ : ℂ) + (-H : ℝ) * I = (σ : ℂ) - (H : ℂ) * I := by push_cast; ring
  simp_rw [he] at hc
  linear_combination hc

lemma lemma56_margin_height_contains_modulus {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) :
    2 * (D : ℝ) ≤ Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hs := lemma56_high_scale_strict_margin hL
  have hU0 := Real.rpow_nonneg (by linarith : 0 ≤ lemma23PaperL D) (9 / 2 : ℝ)
  have hLU : lemma23PaperL D ≤ lemma23PaperL D ^ (9 / 2 : ℝ) := by
    linarith only [hs.2.1, hU0]
  have hDe : (D : ℝ) = Real.exp (lemma23PaperL D) := (Real.exp_log hDp).symm
  have hDU : (D : ℝ) ≤ Real.exp (lemma23PaperL D ^ (9 / 2 : ℝ)) := by
    rw [hDe]
    exact Real.exp_le_exp.mpr hLU
  have h2U : 2 ≤ Real.exp (lemma23PaperL D ^ (9 / 2 : ℝ)) := by
    have he := Real.add_one_le_exp (lemma23PaperL D ^ (9 / 2 : ℝ))
    linarith only [he, hLU, hL]
  calc
    _ ≤ Real.exp (lemma23PaperL D ^ (9 / 2 : ℝ)) *
        Real.exp (lemma23PaperL D ^ (9 / 2 : ℝ)) := by gcongr
    _ = Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

theorem lemma56_uniform_primitive_twisted_gaussian_rectangle_shift :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {B x H τ : ℝ}, 0 < x → 0 ≤ H →
        H ≤ Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2 → |τ| ≤ D →
        let a := 1 - 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))
        I * (∫ t : ℝ in -H..H,
          lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((2 : ℂ) + (t : ℂ) * I)) =
          I * (∫ t : ℝ in -H..H,
            lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((a : ℂ) + (t : ℂ) * I)) +
            (∫ σ : ℝ in a..2,
              lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((σ : ℂ) + (H : ℂ) * I)) -
              (∫ σ : ℝ in a..2,
                lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((σ : ℂ) - (H : ℂ) * I)) := by
  obtain ⟨Dhigh, hhigh⟩ := lemma56_uniform_primitive_margin_zero_exclusion
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Dhigh Drep, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B x H τ hx hH hHmax hτ
  have hf := hhigh χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne
  have hL := (hrep D ((le_max_right _ _).trans hDN)).1
  have hs := lemma56_high_scale_strict_margin hL
  have hVp : 0 < (3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ) :=
    lt_of_lt_of_le (by norm_num) hs.2.2.1
  have hInv : 0 < 1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)) := by positivity
  have hDmax := lemma56_margin_height_contains_modulus hD hL
  apply lemma56_actual_twisted_gaussian_rectangle_shift θ
    (lemma56_primitive_positive_level_nonprincipal θ hθ hq1) B τ hx
    (by linarith only [hInv]) hH
  intro s hre _hσ2 ht
  apply hf (s - (τ : ℂ) * I)
  · simp only [sub_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero, sub_zero]
    have he : 2 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)) =
        2 * (1 / ((3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by ring
    rw [he]
    linarith only [hre, hInv]
  · have hh : |s.im - τ| ≤ |s.im| + |τ| := abs_sub _ _
    have he := Real.exp_pos (2 * lemma23PaperL D ^ (9 / 2 : ℝ))
    simp only [sub_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero]
    linarith only [hh, ht, hτ, hHmax, hDmax, he]


end ZhangLS.Spec
