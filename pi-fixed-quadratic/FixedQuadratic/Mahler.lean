import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace FixedQuadratic

/-- Polynomial Mahler measure for the displayed real quadratic roots. -/
noncomputable def quadraticMahler (a x y : ℝ) : ℝ := a * max 1 |x| * max 1 |y|

/-- The quadratic L² bound, proved here directly without Jensen integration. -/
theorem quadraticMahler_sq_le (a b c x y : ℝ) (_ha : 0 ≤ a)
    (hb : b = -a * (x + y)) (hc : c = a * x * y) :
    (quadraticMahler a x y)^2 ≤ a^2 + b^2 + c^2 := by
  subst b; subst c
  unfold quadraticMahler
  have hx : |x|^2 = x^2 := sq_abs x
  have hy : |y|^2 = y^2 := sq_abs y
  rcases le_total |x| 1 with hx1 | hx1 <;> rcases le_total |y| 1 with hy1 | hy1
  · rw [max_eq_left hx1, max_eq_left hy1]
    nlinarith [sq_nonneg (-a * (x + y)), sq_nonneg (a*x*y)]
  · rw [max_eq_left hx1, max_eq_right hy1]
    nlinarith [sq_nonneg (a*(x*y+1)), sq_nonneg (a*x)]
  · rw [max_eq_right hx1, max_eq_left hy1]
    nlinarith [sq_nonneg (a*(x*y+1)), sq_nonneg (a*y)]
  · rw [max_eq_right hx1, max_eq_right hy1]
    simp only [mul_pow, sq_abs]
    nlinarith [sq_nonneg (-a * (x + y)), sq_nonneg a]

theorem quadraticMahler_le_l2 (a b c x y : ℝ) (ha : 0 ≤ a)
    (hb : b = -a * (x + y)) (hc : c = a * x * y) :
    quadraticMahler a x y ≤ Real.sqrt (a^2 + b^2 + c^2) := by
  have hs := quadraticMahler_sq_le a b c x y ha hb hc
  have hn : 0 ≤ a^2 + b^2 + c^2 := by positivity
  have he := Real.sq_sqrt hn
  have hp := Real.sqrt_nonneg (a^2+b^2+c^2)
  nlinarith

/-- Explicit primitive-max-height coefficient bound; primitivity is unnecessary
for this archimedean inequality. H is a polynomial height, not a Weil height. -/
theorem quadraticMahler_le_sqrt_three_height (a b c x y H : ℝ)
    (ha : 0 ≤ a) (hH : 0 ≤ H) (haH : a ≤ H) (hbH : |b| ≤ H) (hcH : |c| ≤ H)
    (hb : b = -a * (x+y)) (hc : c = a*x*y) :
    quadraticMahler a x y ≤ Real.sqrt 3 * H := by
  have hs := quadraticMahler_sq_le a b c x y ha hb hc
  have ha2 : a^2 ≤ H^2 := by nlinarith
  have hb2 : b^2 ≤ H^2 := by nlinarith [sq_abs b, abs_nonneg b]
  have hc2 : c^2 ≤ H^2 := by nlinarith [sq_abs c, abs_nonneg c]
  have he : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 3 * H := mul_nonneg (Real.sqrt_nonneg _) hH
  nlinarith

end FixedQuadratic
