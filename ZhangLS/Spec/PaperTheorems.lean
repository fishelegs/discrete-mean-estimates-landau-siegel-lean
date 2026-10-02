import ZhangLS.Spec.RealAxisLFunction

/-!
# Paper-level theorem specifications

These declarations state the mathematical targets.  They are intentionally separated
from the proof implementation, so a future proof cannot weaken the theorem statement
merely to make Lean close the goal.
-/

namespace ZhangLS.Spec

/-- The quantitative content of Zhang's Theorem 1 for a chosen absolute constant.

The paper states existence of an absolute effectively computable `c₁ > 0`.  Effective
computability is tracked separately as proof metadata until the project has selected a
formal computability representation for explicit real constants.
-/
def Theorem1AtConstant (c₁ : ℝ) : Prop :=
  0 < c₁ ∧
    ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      1 < D →
      c₁ * (Real.log (D : ℝ)) ^ (-2022 : ℤ) < realLAtOne χ

/-- Mathematical target of Theorem 1, excluding the yet-to-be-formalized metadata
assertion that the witness is effectively computable. -/
def Theorem1Target : Prop :=
  ∃ c₁ : ℝ, Theorem1AtConstant c₁

/-- Quantitative zero-free-region statement corresponding to the paper's Theorem 2.
`σ` is real, embedded into `ℂ` when evaluating the analytic L-function. -/
def Theorem2AtConstant (c₂ : ℝ) : Prop :=
  0 < c₂ ∧
    ∀ {D : ℕ} (χ : RealPrimitiveCharacter D) (σ : ℝ),
      1 < D →
      1 - c₂ * (Real.log (D : ℝ)) ^ (-2024 : ℤ) < σ →
      dirichletLFunction χ (σ : ℂ) ≠ 0

/-- Mathematical target of Theorem 2, again separating mathematical existence from
formal metadata about effective computability of the absolute constant. -/
def Theorem2Target : Prop :=
  ∃ c₂ : ℝ, Theorem2AtConstant c₂

end ZhangLS.Spec
