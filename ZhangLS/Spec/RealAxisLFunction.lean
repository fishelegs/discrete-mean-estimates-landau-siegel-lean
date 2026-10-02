import ZhangLS.Spec.DirichletLSeries

/-!
# Real-axis interface for Dirichlet L-functions

The paper compares `L(1, χ)` and `L'(1, χ)` as real numbers.  The underlying
mathlib analytic continuation is complex-valued, so this file makes the real-axis
projection explicit and records the exact compatibility theorem that still has to
be proved.

Crucially, we do *not* identify the real derivative with the complex derivative by
definition.  That identification is a theorem, and must follow from the fact that a
real Dirichlet character has a real-valued L-function on the real axis.
-/

namespace ZhangLS.Spec

/-- Real part of the analytically continued L-function on the real axis. -/
noncomputable def realLValue {D : ℕ} (χ : RealPrimitiveCharacter D) (x : ℝ) : ℝ :=
  (dirichletLFunction χ (x : ℂ)).re

/-- The paper's real number `L(1, χ)`. -/
noncomputable def realLAtOne {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  realLValue χ 1

/-- Derivative along the real axis.  This is intentionally distinct from the
complex derivative until compatibility has been proved. -/
noncomputable def realLDerivAtOne {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  deriv (realLValue χ) 1

@[simp] theorem realLAtOne_eq_re {D : ℕ} (χ : RealPrimitiveCharacter D) :
    realLAtOne χ = (LAtOne χ).re := by
  rfl

/-- Exact analytic bridge required before replacing the real derivative by the
complex derivative in arithmetic inequalities.  This is a specification, not an
assumption attached to the character. -/
def RealAxisAnalyticCompatibility {D : ℕ} (χ : RealPrimitiveCharacter D) : Prop :=
  (∀ x : ℝ, (dirichletLFunction χ (x : ℂ)).im = 0) ∧
    ((LDerivAtOne χ).im = 0) ∧
    realLDerivAtOne χ = (LDerivAtOne χ).re

/-- The first concrete analytic milestone for Step 04. -/
def RealAxisValueTheoremTarget : Prop :=
  ∀ {D : ℕ} (χ : RealPrimitiveCharacter D), 1 < D →
    ∀ x : ℝ, (dirichletLFunction χ (x : ℂ)).im = 0

/-- The derivative-compatibility milestone, to be proved only after the real-axis
value theorem. -/
def RealAxisDerivativeTheoremTarget : Prop :=
  ∀ {D : ℕ} (χ : RealPrimitiveCharacter D), 1 < D →
    (LDerivAtOne χ).im = 0 ∧ realLDerivAtOne χ = (LDerivAtOne χ).re

end ZhangLS.Spec

namespace ZhangLS.Spec

/-- Zhang's small-value contradiction hypothesis, expressed in the real interface. -/
def AssumptionAWithConstant {D : ℕ} (χ : RealPrimitiveCharacter D) (c₁ : ℝ) : Prop :=
  realLAtOne χ < c₁ * (Real.log (D : ℝ)) ^ (-2022 : ℤ)

/-- Normalized small-value hypothesis, used only after a quantitative reduction
justifies the constant `1`. -/
def NormalizedAssumptionA {D : ℕ} (χ : RealPrimitiveCharacter D) : Prop :=
  AssumptionAWithConstant χ 1

end ZhangLS.Spec
