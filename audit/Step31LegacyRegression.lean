import ZhangLS.Basic
import ZhangLS.RealRoucheTailBound
import ZhangLS.RealStrictCalculusIntegral
import ZhangLS.RealCompactAngleCoverage
import ZhangLS.BadCharacterDensity
import ZhangLS.AssumptionA

/-! A counterexample to the old Taylor absorption statement without a sign bound. -/

example : (0 : ℝ) ≤ 2 * (-1 : ℝ)^2 ∧ (-1 : ℝ) ≤ 1 / 10 ∧
    ¬ ((0 : ℝ) ≤ (1 / 5) * (-1 : ℝ)) := by
  norm_num

example (q b : ℝ) (hq : q ≤ 2 * b^2) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 10) :
    q ≤ (1 / 5) * b :=
  ZhangLS.taylor_truncation_absorbed_linear q b hq hb0 hb

example : (2 : ℝ) * Real.pi ≤ 7 := ZhangLS.two_pi_length_bound

example (x : ℝ) (hx : x = 1) : 1 + x - 2 = 0 :=
  ZhangLS.antideriv_log_cross_cancel x hx

example (x : ℝ) (hx : x ≤ 1 + 2) : x ≤ 3 := by
  have h : x ≤ 1.0 + 2.0 := by norm_num at hx ⊢; exact hx
  have hbound := ZhangLS.Proposition_2_1_Union_Bound x h
  norm_num at hbound
  exact hbound
