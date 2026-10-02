import ZhangLS.Spec.Lemma57CompletedDirichletStripBounds

/-!
# Step 44 completed Dirichlet L strip regression

Pins the strong FE-pair bound and its odd Hurwitz and Dirichlet L consequences.
-/

namespace ZhangLS.Spec

open Complex

example (P : StrongFEPair ℂ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ), a ≤ σ → σ ≤ b →
      ‖P.Λ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  StrongFEPair.exists_norm_Λ_le_on_verticalStrip P a b

example (a : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖HurwitzZeta.completedHurwitzZetaOdd a
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  exists_completedHurwitzZetaOdd_norm_le_criticalStrip a

example {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖ZMod.completedLFunction₀ Φ
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  exists_ZMod_completedLFunction₀_norm_le_criticalStrip Φ

example {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖DirichletCharacter.completedLFunction χ.chi
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  exists_completedDirichletL_norm_le_criticalStrip χ hD

end ZhangLS.Spec
