import ZhangLS.Spec.Lemma47ThreeZeros

/-! Original-statement and trusted-axiom regression for Lemma 4.7. -/

namespace ZhangLS.Spec

open Complex Metric Set

/-- All inputs are the original good-character and critical-line-zero
hypotheses. The expansion constant and modulus threshold are uniform. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    ρ.re = 1 / 2 →
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
    lemma45ActualA χ ψ ρ = 0 →
    let f := fun w => lemma45ActualA χ ψ (ρ + w)
    let R := lemma44PaperAlpha D * (1 + c * lemma44PaperAlpha D * lemma23PaperL D)
    lemma44PaperAlpha D < R ∧ R < 2 * lemma44PaperAlpha D ∧
    (∀ w ∈ sphere (0 : ℂ) R, f w ≠ 0) ∧
    (∑ z ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
      (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
      (((MeromorphicOn.divisor f (closedBall 0 R)) z).toNat : ℂ)) = 3 := by
  simpa only [Lemma47Target, lemma47OuterRadius] using lemma47_proved

/-- The analytic comparison covers the entire radius-2α disk, including
the left cap outside the original approximate-equation region. -/
example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ w : ℂ} (hre : ρ.re = 1 / 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0) (hw : ‖w‖ < 2 * lemma44PaperAlpha D) :
    ‖lemma45ActualA χ ψ (ρ + w) -
      lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w‖ ≤
        lemma47ModelErrorConstant * lemma44PaperAlpha D * lemma23PaperL D := by
  exact lemma47_actual_model_approximation χ ψ hD hψ hre him hzero hw

#print axioms lemma47_dirichletZ_reflection
#print axioms lemma47_actual_Z_reflection
#print axioms lemma47_actual_normalized_reflection
#print axioms lemma47_actual_A_analyticOn_outer_disk
#print axioms lemma47_actual_error_reflection
#print axioms lemma47_actual_model_approximation
#print axioms lemma47_model_uniform_outer_boundary
#print axioms lemma47_actual_strict_outer_comparison
#print axioms lemma47_actual_three_zeros_at_expansion
#print axioms lemma47_proved

end ZhangLS.Spec
