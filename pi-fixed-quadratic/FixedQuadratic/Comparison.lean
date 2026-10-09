import Mathlib.Tactic
namespace FixedQuadratic

/-- Comparison of the two explicit budgets. This proves a scalar contradiction,
not a pi theorem: producing the arithmetic/analytic estimates is separate work. -/
theorem comparison_contradiction (ν θ A η b cL Ea En δ ε t : ℝ)
    (hν : 1 ≤ ν) (hb : b ≤ θ)
    (hlower : -(1-b)-Ea-δ ≤ t)
    (hupper : t ≤ En+ε+max (-cL) (-ν*(A*(1-η)-b)))
    (hgap : Ea+En+δ+ε < ν*(A*(1-η)-θ)-(1-θ))
    (hcollision : 1+Ea+En+δ+ε < cL) (hb0 : 0 ≤ b) : False := by
  have hendpoint : ν*(A*(1-η)-θ)-(1-θ) ≤ ν*(A*(1-η)-b)-(1-b) := by
    nlinarith
  rcases le_total (-cL) (-ν*(A*(1-η)-b)) with h | h
  · rw [max_eq_right h] at hupper
    linarith
  · rw [max_eq_left h] at hupper
    linarith

end FixedQuadratic
