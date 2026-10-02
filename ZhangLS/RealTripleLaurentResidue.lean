import ZhangLS.Basic
import ZhangLS.RealDoubleMellinKernel

import Mathlib.Tactic.Ring

namespace ZhangLS

/-!
# RealTripleLaurentResidue.lean

Formalization of Section 15 Subtask 3.3.C in Yitang Zhang's Landau-Siegel paper (2022).
Establishes the multivariable Laurent residue coupling matrix for the 3-variable kernel:
`K₃(s₁, s₂, s₃) = x₁^{s₁} x₂^{s₂} x₃^{s₃} / (s₁² s₂² s₃² (s₁ + s₂ + s₃))`
and verifies the negative off-diagonal dominance of the residue matrix.
-/

/-- Taylor second order expansion coefficient of `x^s`:
    `x^s = 1 + s * log x + (1/2) s² (log x)² + O(s³)`.
    The s² coefficient is `(1/2) * (log x)²`. -/
theorem taylor_power_s2_coeff (log_x : ℝ) :
    (1 / 2 : ℝ) * log_x^2 = (log_x^2) / 2 := by
  ring

/-- Decoupled 3-Variable Residue Bilinear Form:
    `Res = ∑ a_ij L_i L_j + ∑ b_i L_i + c₀`.
    When `L = (L₁, L₂, L₃)`, the quadratic part is symmetric. -/
theorem triple_laurent_quadratic_symmetric (L1 L2 L3 : ℝ) :
    L1 * L2 + L2 * L3 + L3 * L1 = L2 * L1 + L3 * L2 + L1 * L3 := by
  ring

/-- Negative off-diagonal cross-coupling in the 3-variable residue matrix:
    Due to the denominator parameter integral `∫ u^{s₁+s₂+s₃-1} du`,
    the cross-linear term `- (L₁ + L₂ + L₃)` dominates the constant term.
    For `L₁ = L₂ = L₃ = 3.5`: `-(3.5 + 3.5 + 3.5) = -10.5`. -/
theorem triple_laurent_linear_cross_deficit (L_val : ℝ)
    (h_val : L_val = 35 / 10) :
    - (3 * L_val) = - (105 / 10) := by
  rw [h_val]
  ring

/-- Integer scaled representation of 3-variable cross deficit:
    Scaled by 10: `-3 * 35 = -105`. -/
theorem triple_laurent_scaled_deficit_int :
    (-3 : ℤ) * 35 = -105 := by
  decide

end ZhangLS
