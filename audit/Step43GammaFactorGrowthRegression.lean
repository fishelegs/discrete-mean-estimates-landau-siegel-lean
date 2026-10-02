import ZhangLS.Spec.Lemma57GammaFactorGrowth

/-!
# Step 43 reciprocal-Gamma and ordinary-zeta growth regression

This check pins the positive-strip Gamma estimate, the reciprocal-Gamma
exponential estimate, and the resulting ordinary-zeta bound.
-/

namespace ZhangLS.Spec

open Complex

example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ), a ≤ σ → σ ≤ b →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  exists_norm_Gamma_le_on_verticalStrip_of_pos a b ha hab

example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ), a ≤ σ → σ ≤ b →
      ‖(Complex.Gamma ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t|) :=
  exists_norm_Gamma_inv_le_exp_on_verticalStrip a b ha hab hb

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
    (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
    ‖(Gammaℝ ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
      C * Real.exp (Real.pi * |t| / 2) :=
  exists_norm_Gammaℝ_inv_le_exp_on_criticalStrip

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
    (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
    (1 : ℝ) / 2 ≤ ‖1 - ((σ : ℂ) + (t : ℂ) * I)‖ →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      C * Real.exp (Real.pi * |t| / 2) :=
  exists_riemannZeta_norm_le_exp_on_criticalStrip_away

end ZhangLS.Spec
