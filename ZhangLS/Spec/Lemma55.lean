import ZhangLS.Spec.Lemma55LocalUniqueness

/-!
# Original Lemma 5.5: faithful target

The original full region, whose height grows as 2D, is retained exactly.
The simple real zero and local uniqueness follow from actual (A) and
Lemma 5.7. The complete original target is proved in
ZhangLS.Spec.Lemma55FullZeroExclusion, without a cyclic target import.
-/

namespace ZhangLS.Spec

/-- The entire original zero-exclusion region of Lemma 5.5. -/
def Lemma55InZeroRegion (D : ℕ) (s : ℂ) : Prop :=
  1 - 2 / Real.log (D : ℝ) < s.re ∧ |s.im| < 2 * (D : ℝ)

/-- All constants and the conductor threshold are uniform in χ and s. -/
def Lemma55AtConstant (C : ℝ) : Prop :=
  0 < C ∧ ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∃ ρ : ℝ, 0 < 1 - ρ ∧
        1 - ρ ≤ C * Real.log (D : ℝ) ^ (-2022 : ℤ) ∧
        dirichletLFunction χ (ρ : ℂ) = 0 ∧
        deriv (dirichletLFunction χ) (ρ : ℂ) ≠ 0 ∧
        ∀ s : ℂ, Lemma55InZeroRegion D s →
          dirichletLFunction χ s = 0 → s = (ρ : ℂ)

def Lemma55Target : Prop := ∃ C : ℝ, Lemma55AtConstant C

end ZhangLS.Spec
