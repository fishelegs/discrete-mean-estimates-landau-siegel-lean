import ZhangLS.Spec.Lemma57ShiftedGammaGrowth

/-!
# Step 45 shifted Gamma and contour-growth regression

Pins the shifted odd Gamma estimate, ordinary Dirichlet L growth, and the
unconditional critical-strip growth and contour-shift statements.
-/

namespace ZhangLS.Spec

open Complex

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
    (3 : ℝ) / 4 ≤ σ → σ ≤ (5 : ℝ) / 4 →
    ‖(Complex.Gamma ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
      C * Real.exp (Real.pi * |t|) :=
  exists_norm_Gamma_inv_le_exp_on_midStrip

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
    (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
    ‖(Gammaℝ (((σ : ℂ) + (t : ℂ) * I) + 1))⁻¹‖ ≤
      C * Real.exp (Real.pi * |t| / 2) :=
  exists_norm_Gammaℝ_shifted_inv_le_exp_on_criticalStrip

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖dirichletLFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (Real.pi * |t| / 2) :=
  exists_dirichletLFunction_norm_le_exp_on_criticalStrip χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57CriticalStripExponentialGrowth χ :=
  lemma57CriticalStripExponentialGrowth_unconditional χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_unconditional χ hD

end ZhangLS.Spec
