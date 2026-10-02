import ZhangLS.Spec.Lemma56PerronWindowLeft

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_rectangle_norm_budget {R L T Q : ℂ}
    (hshift : I * R = I * L + T - Q) : ‖R‖ ≤ ‖L‖ + ‖T‖ + ‖Q‖ := by
  calc
    _ = ‖I * R‖ := by simp
    _ = ‖I * L + T - Q‖ := congrArg norm hshift
    _ ≤ ‖I * L + T‖ + ‖Q‖ := norm_sub_le _ _
    _ ≤ (‖I * L‖ + ‖T‖) + ‖Q‖ := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by simp

end ZhangLS.Spec
