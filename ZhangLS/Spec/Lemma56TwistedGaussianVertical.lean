import ZhangLS.Spec.Lemma56GaussianNorm

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_twisted_gaussian_vertical_intervalIntegrable {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (B τ σ : ℝ)
    {x H : ℝ} (hx : 0 < x) (hH : 0 ≤ H)
    (hfree : ∀ t : ℝ, |t| ≤ H →
      DirichletCharacter.LFunction θ ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => lemma56TwistedGaussianArithmeticIntegrand θ B x τ
      ((σ : ℂ) + (t : ℂ) * I)) volume (-H) H := by
  have hc : ContinuousOn (fun t : ℝ => lemma56TwistedGaussianArithmeticIntegrand θ B x τ
      ((σ : ℂ) + (t : ℂ) * I)) (Set.Icc (-H) H) := by
    intro t ht
    have hAt := lemma56_actual_twisted_gaussian_integrand_analyticAt θ hθ B τ hx
      (hfree t (abs_le.mpr ht))
    have hline : ContinuousAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) t := by fun_prop
    exact (ContinuousAt.comp (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I)
      hAt.continuousAt hline).continuousWithinAt
  exact hc.intervalIntegrable_of_Icc (by linarith only [hH])

lemma lemma56_twisted_gaussian_vertical_integral_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x H M : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (τ σ : ℝ)
    (hLD : ∀ t : ℝ, |t| ≤ H →
      ‖logDeriv (DirichletCharacter.LFunction θ)
        ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ ≤ M) :
    ‖∫ t : ℝ in -H..H, lemma56TwistedGaussianArithmeticIntegrand θ B x τ
      ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        M * (2 * Real.pi * x ^ σ * Real.exp (σ ^ 2 / (4 * B ^ 2))) := by
  let g : ℝ → ℝ := fun t => M * ‖lemma56GaussianKernel B σ x t‖
  have hg : Integrable g := (lemma56_gaussian_kernel_integrable hB σ hx).norm.const_mul M
  calc
    _ ≤ ∫ t : ℝ in -H..H, g t := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by linarith only [hH])
      · filter_upwards [] with t ht
        have habs : |t| ≤ H := abs_le.mpr ⟨ht.1.le, ht.2⟩
        have hn : ‖lemma56TwistedGaussianArithmeticIntegrand θ B x τ
            ((σ : ℂ) + (t : ℂ) * I)‖ =
          ‖logDeriv (DirichletCharacter.LFunction θ)
            ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ *
              ‖lemma56GaussianKernel B σ x t‖ := by
          simp only [lemma56TwistedGaussianArithmeticIntegrand, lemma56GaussianKernel,
            norm_mul, norm_neg, mul_assoc]
        rw [hn]
        exact mul_le_mul_of_nonneg_right (hLD t habs) (norm_nonneg _)
      · exact hg.intervalIntegrable
    _ ≤ ∫ t : ℝ, g t := by
      rw [intervalIntegral.integral_of_le (by linarith only [hH])]
      exact MeasureTheory.setIntegral_le_integral hg (Filter.Eventually.of_forall
        (fun t => mul_nonneg hM (norm_nonneg _)))
    _ = _ := by
      rw [MeasureTheory.integral_const_mul, lemma56_gaussian_kernel_norm_integral hB hx]

theorem lemma56_uniform_primitive_twisted_gaussian_left_bound :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ {B x H τ : ℝ}, 0 < B → 0 < x → 0 ≤ H →
        H ≤ Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) / 2 → |τ| ≤ D →
        let V := (3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)
        let a := 1 - 1 / V
        IntervalIntegrable (fun t : ℝ => lemma56TwistedGaussianArithmeticIntegrand θ B x τ
          ((a : ℂ) + (t : ℂ) * I)) volume (-H) H ∧
        ‖∫ t : ℝ in -H..H, lemma56TwistedGaussianArithmeticIntegrand θ B x τ
          ((a : ℂ) + (t : ℂ) * I)‖ ≤
            (24 * V ^ 2 + 28800 * V) *
              (2 * Real.pi * x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2))) := by
  obtain ⟨Dld, hld⟩ := lemma56_uniform_primitive_margin_logDeriv_bound
  obtain ⟨Dzero, hzero⟩ := lemma56_uniform_primitive_margin_zero_exclusion
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max (max Dld Dzero) Drep, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne B x H τ hB hx hH hHmax hτ
  have hLD := hld χ θ ((le_max_left _ _).trans ((le_max_left _ _).trans hDN))
    hD hA hθ hq1 hqT hne
  have hfree := hzero χ θ ((le_max_right _ _).trans ((le_max_left _ _).trans hDN))
    hD hA hθ hq1 hqT hne
  have hL := (hrep D ((le_max_right _ _).trans hDN)).1
  have hs := lemma56_high_scale_strict_margin hL
  let V := (3 / 4 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)
  let a := 1 - 1 / V
  have hVp : 0 < V := lt_of_lt_of_le (by norm_num) hs.2.2.1
  have hInv : 0 < 1 / V := by positivity
  have hDmax := lemma56_margin_height_contains_modulus hD hL
  have hheight (t : ℝ) (ht : |t| ≤ H) : |t - τ| ≤
      Real.exp (2 * lemma23PaperL D ^ (9 / 2 : ℝ)) := by
    have hh := abs_sub t τ
    linarith only [hh, ht, hτ, hHmax, hDmax]
  have hre (t : ℝ) : ((a : ℂ) + (t : ℂ) * I - (τ : ℂ) * I).re = a := by simp
  have him (t : ℝ) : ((a : ℂ) + (t : ℂ) * I - (τ : ℂ) * I).im = t - τ := by simp
  have hlocalLD (t : ℝ) (ht : |t| ≤ H) :
      ‖logDeriv (DirichletCharacter.LFunction θ)
        ((a : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ ≤ 24 * V ^ 2 + 28800 * V := by
    apply hLD
    · rw [hre]
    · rw [hre]; dsimp [a]; linarith only [hInv]
    · rw [him]; exact hheight t ht
  constructor
  · apply lemma56_twisted_gaussian_vertical_intervalIntegrable θ
      (lemma56_primitive_positive_level_nonprincipal θ hθ hq1) B τ a hx hH
    intro t ht
    apply hfree
    · rw [hre]
      change 1 - 2 / V < a
      dsimp [a]
      have he : 2 / V = 2 * (1 / V) := by ring
      rw [he]
      linarith only [hInv]
    · rw [him]
      have he := Real.exp_pos (2 * lemma23PaperL D ^ (9 / 2 : ℝ))
      linarith only [hheight t ht, he]
  · exact lemma56_twisted_gaussian_vertical_integral_bound θ hB hx hH
      (by positivity) τ a hlocalLD


end ZhangLS.Spec
