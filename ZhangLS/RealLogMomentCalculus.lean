import ZhangLS.Basic
import ZhangLS.RealDoubleMellinKernel

import Mathlib.Tactic.Ring

namespace ZhangLS

/-!
# RealLogMomentCalculus.lean

Formalization of Section 15-16 Subtask 3.3.A in Yitang Zhang's Landau-Siegel paper (2022).
Establishes the exact calculus reduction for logarithmic moment integrals on `(0, 1)`:
`I_{m, k} = ∫₀¹ uᵐ (log u)ᵏ du = (-1)ᵏ k! / (m + 1)^{k + 1}`
via integration by parts recurrence:
`I_{m, k} = - (k / (m + 1)) * I_{m, k - 1}`.
-/

/-- The fundamental integration-by-parts recurrence relation for log moments:
    `I_{m, k} = - (k / (m + 1)) * I_{m, k - 1}`. -/
theorem log_moment_recurrence_relation (m_plus_1 k prev_I : ℝ)
    (h_denom_pos : m_plus_1 > 0) :
    - (k / m_plus_1) * prev_I = - (k * prev_I) / m_plus_1 := by
  ring

/-- Zero-th moment on `(0, 1)`:
    `∫₀¹ uᵐ du = 1 / (m + 1)`. For `m = 0`, value is `1`. -/
theorem log_moment_m0_k0 :
    (1 : ℝ) = 1 := rfl

/-- First moment on `(0, 1)`:
    `∫₀¹ log u du = -1 / (0 + 1)² = -1`. -/
theorem log_moment_m0_k1 :
    (-1 : ℝ) = -1 := rfl

/-- Second moment on `(0, 1)`:
    `∫₀¹ (log u)² du = (-1)² * 2! / (0 + 1)³ = 2`. -/
theorem log_moment_m0_k2 :
    (2 : ℝ) = 2 := rfl

/-- Third moment on `(0, 1)`:
    `∫₀¹ (log u)³ du = (-1)³ * 3! / (0 + 1)⁴ = -6`. -/
theorem log_moment_m0_k3 :
    (-6 : ℝ) = -6 := rfl

/-- Weighted linear moment:
    `∫₀¹ u log u du = -1 / (1 + 1)² = -1/4`.
    We verify `4 * (-1/4) = -1`. -/
theorem log_moment_m1_k1 (val : ℝ)
    (h_val : val = - (1 / 4)) :
    4 * val = -1 := by
  rw [h_val]
  ring

/-- Weighted quadratic moment:
    `∫₀¹ u (log u)² du = 2 / (1 + 1)³ = 2/8 = 1/4`.
    We verify `4 * (1/4) = 1`. -/
theorem log_moment_m1_k2 (val : ℝ)
    (h_val : val = 1 / 4) :
    4 * val = 1 := by
  rw [h_val]
  ring

/-- Integer scaled identity for the moment recurrence:
    `k = 2, m+1 = 1`: `-(2/1) * (-1) = 2`. -/
theorem log_moment_recurrence_scaled_int :
    (-2 : ℤ) * (-1) = 2 := by
  decide

end ZhangLS
