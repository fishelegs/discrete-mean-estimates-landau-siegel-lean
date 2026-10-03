import ZhangLS.Spec.AppendixBTailMultiplier
import ZhangLS.Spec.AppendixBKernelErrorDecay

/-! Decay of the explicit transferred contour budget. The actual full-tail
comparison is a separate assembly obligation; it is not assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Filter Topology

noncomputable def appendixBTailContourBudget (D : ℕ) : ℝ :=
  (6*Real.exp 1*lemma23PaperL D^15)*appendixBContourBudget D

lemma appendixB_tail_contour_budget_polynomial {D : ℕ}
    (hL : 2000≤lemma23PaperL D) :
    appendixBTailContourBudget D≤
      (6*Real.exp 1*appendixBContourPolynomialConstant)*lemma23PaperL D^42*
        Real.exp (-(lemma23PaperL D^(1/10 : ℝ))) := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hh := mul_le_mul_of_nonneg_left (appendixB_contour_budget_polynomial hL)
    (show 0≤6*Real.exp 1*lemma23PaperL D^15 by positivity)
  apply hh.trans_eq
  ring

/-- Every fixed inverse-log power is available for the transferred budget;
the L^15 Gaussian cost does not compromise contour decay. -/
theorem appendixB_tail_contour_budget_eventual_power (N : ℕ) :
    ∀ᶠ D : ℕ in atTop, 0≤appendixBTailContourBudget D ∧
      appendixBTailContourBudget D≤lemma23PaperL D^(-(N : ℤ)) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hC : 0<6*Real.exp 1*appendixBContourPolynomialConstant := by
    unfold appendixBContourPolynomialConstant
    positivity [Real.pi_pos]
  have he := ht.eventually (lemma84_stretched_exponential_absorption _ hC 42 N)
  filter_upwards [ht.eventually_ge_atTop 2000,he] with D hL he
  have hLp : 0<lemma23PaperL D := by linarith
  refine ⟨?_,(appendixB_tail_contour_budget_polynomial hL).trans he⟩
  unfold appendixBTailContourBudget
  exact mul_nonneg (by positivity) (appendixB_contour_budget_nonneg hLp)

end ZhangLS.Spec
