import ZhangLS.Spec.Lemma56GaussianMarginBudget

/-! # Actual oscillatory Gaussian estimates for Lemma 5.6

The original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_twisted_gaussian_horizontal_point_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x σ η M : ℝ} (hB : 0 < B) (hx : 1 ≤ x)
    (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) (τ : ℝ)
    (hLD : ‖logDeriv (DirichletCharacter.LFunction θ)
      ((σ : ℂ) + (η : ℂ) * I - (τ : ℂ) * I)‖ ≤ M) :
    ‖lemma56TwistedGaussianArithmeticIntegrand θ B x τ ((σ : ℂ) + (η : ℂ) * I)‖ ≤
      M * x ^ 2 * (Real.sqrt Real.pi / B) * Real.exp ((4 - η ^ 2) / (4 * B ^ 2)) := by
  have hxp : 0 < x := by linarith only [hx]
  have hM : 0 ≤ M := (norm_nonneg _).trans hLD
  have hpow : x ^ σ ≤ x ^ (2 : ℕ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx hσ2
  have hs2 : σ ^ 2 ≤ 4 := by nlinarith only [hσ0, hσ2]
  have hex : (σ ^ 2 - η ^ 2) / (4 * B ^ 2) ≤ (4 - η ^ 2) / (4 * B ^ 2) := by
    gcongr
  rw [lemma56TwistedGaussianArithmeticIntegrand, norm_mul, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hxp, lemma56_gaussian_omega_norm hB]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ M * x ^ 2 * ((Real.sqrt Real.pi / B) *
      Real.exp ((4 - η ^ 2) / (4 * B ^ 2))) := by gcongr
    _ = _ := by ring

lemma lemma56_twisted_gaussian_horizontal_integral_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x a η M : ℝ} (hB : 0 < B) (hx : 1 ≤ x)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (τ : ℝ)
    (hLD : ∀ σ : ℝ, a ≤ σ → σ ≤ 2 →
      ‖logDeriv (DirichletCharacter.LFunction θ)
        ((σ : ℂ) + (η : ℂ) * I - (τ : ℂ) * I)‖ ≤ M) :
    ‖∫ σ : ℝ in a..2, lemma56TwistedGaussianArithmeticIntegrand θ B x τ
      ((σ : ℂ) + (η : ℂ) * I)‖ ≤
        (2 - a) * (M * x ^ 2 * (Real.sqrt Real.pi / B) *
          Real.exp ((4 - η ^ 2) / (4 * B ^ 2))) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => lemma56TwistedGaussianArithmeticIntegrand θ B x τ
      ((σ : ℂ) + (η : ℂ) * I))
    (C := M * x ^ 2 * (Real.sqrt Real.pi / B) * Real.exp ((4 - η ^ 2) / (4 * B ^ 2)))
    (a := a) (b := 2) (by
      intro σ hσ
      have hs : σ ∈ Set.Ioc a 2 := by simpa only [Set.uIoc_of_le ha2] using hσ
      exact lemma56_twisted_gaussian_horizontal_point_bound θ hB hx (ha0.trans hs.1.le)
        hs.2 τ (hLD σ hs.1.le hs.2))
  rw [abs_of_nonneg (by linarith only [ha2] : 0 ≤ 2 - a)] at hb
  exact hb.trans_eq (by ring)


end ZhangLS.Spec
