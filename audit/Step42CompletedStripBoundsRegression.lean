import ZhangLS.Spec.Lemma57CompletedStripBounds

/-!
# Step 42 completed-strip bounds regression

This check pins the general uniform strip bound for completed Mellin transforms
and its two Riemann-zeta consequences.
-/

namespace ZhangLS.Spec

open Complex

example (P : WeakFEPair ℂ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ), a ≤ σ → σ ≤ b →
      ‖P.Λ₀ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  WeakFEPair.exists_norm_Λ₀_le_on_verticalStrip P a b

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
    (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
    ‖completedRiemannZeta₀ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  exists_completedRiemannZeta₀_norm_le_criticalStrip

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
    (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
    (1 : ℝ) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ →
    (1 : ℝ) / 2 ≤ ‖1 - ((σ : ℂ) + (t : ℂ) * I)‖ →
    ‖completedRiemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  exists_completedRiemannZeta_norm_le_criticalStrip_away

end ZhangLS.Spec
