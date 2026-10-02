import ZhangLS.Spec.Lemma46ZeroAnalysis

/-! Original-statement and trusted-axiom regression for Lemma 4.6. -/

namespace ZhangLS.Spec

open Complex

/-- The contraction constant and modulus threshold precede all
characters and zeros. The gap radius is explicitly positive. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    1 / 2 ≤ ρ.re → ρ.re < 1 / 2 + lemma44PaperAlpha D ^ 2 →
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
    lemma45ActualA χ ψ ρ = 0 →
    0 < lemma44PaperAlpha D *
      (1 - c * lemma44PaperAlpha D * lemma23PaperL D) ∧
    ρ.re = 1 / 2 ∧ deriv (lemma45ActualA χ ψ) ρ ≠ 0 ∧
    ∀ w : ℂ, 0 < ‖w‖ →
      ‖w‖ < lemma44PaperAlpha D * (1 - c * lemma44PaperAlpha D * lemma23PaperL D) →
      lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) ≠ 0 := by
  simpa only [Lemma46Target, lemma46InnerRadius] using lemma46_proved

#print axioms lemma46_inverse_F_logDeriv
#print axioms lemma46_equation411
#print axioms lemma46_exponential_transport_on_ball
#print axioms lemma46_actual_model_approximation
#print axioms lemma46_model_uniform_inner_boundary
#print axioms lemma46_actual_A_reflected_zero
#print axioms lemma46_unique_simple_zero_of_count_one
#print axioms lemma46_actual_rouche_count_one
#print axioms lemma46_zero_analysis_at_contraction
#print axioms lemma46_exists_contraction_threshold
#print axioms lemma46_proved

end ZhangLS.Spec
