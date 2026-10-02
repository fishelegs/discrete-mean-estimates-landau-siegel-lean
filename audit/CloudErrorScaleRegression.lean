import ZhangLS.Spec.PaperErrorScaleBudget

namespace ZhangLS.Spec
example {D : ℕ} (hL : 0 < Real.log (D : ℝ)) :
    Real.log (Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ))) /
      Real.log (Real.exp ((Real.log (D : ℝ)) ^ 9)) =
        Real.log (D : ℝ) ^ (-79 / 10 : ℝ) := paper_logT_div_logP hL

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {C : ℝ} {e : ℂ}
    (he : ‖e‖ ≤ C * (Real.pi / Real.log (Real.exp ((Real.log (D : ℝ)) ^ 9)))) :
    ‖LDerivAtOne χ ^ 2 * e‖ ≤ ((16 * Real.exp 1)^2 * C * Real.pi) *
      Real.log (D : ℝ) ^ (-5 : ℤ) := paper_actual_LDeriv_error_budget χ hD hL he

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {C : ℝ} (hC : 0 ≤ C) {e : ℂ}
    (he : ‖e‖ ≤ C * (Real.log (Real.exp ((Real.log (D : ℝ)) ^ (11 / 10 : ℝ))) /
      Real.log (Real.exp ((Real.log (D : ℝ)) ^ 9)))) :
    ‖LDerivAtOne χ ^ 2 * e‖ ≤ ((16 * Real.exp 1)^2 * C) *
      Real.log (D : ℝ) ^ (-3 : ℤ) := paper_actual_LDeriv_boundary_budget χ hD hL hC he
end ZhangLS.Spec

#print axioms ZhangLS.Spec.paper_logT_div_logP
#print axioms ZhangLS.Spec.paper_alpha_logT
#print axioms ZhangLS.Spec.paper_boundary_scale_le_L7
#print axioms ZhangLS.Spec.paper_alpha_eq_L9
#print axioms ZhangLS.Spec.paper_actual_LDeriv_error_budget
#print axioms ZhangLS.Spec.paper_actual_LDeriv_boundary_budget
