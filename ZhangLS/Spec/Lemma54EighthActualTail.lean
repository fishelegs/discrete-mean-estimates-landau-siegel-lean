import ZhangLS.Spec.Lemma54EighthHeightTail

/-! # Integrating the actual δ against a bounded prime-sum function

This is the analytic glue from the actual eighth-order δ estimate to a
central finite-height cancellation bound and its H⁻⁷ tail.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set

/-- The actual Mellin transform is continuous along Re(s)=1. -/
theorem lemma54_eighth_actual_line_continuous {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) :
    Continuous (fun t : ℝ => lemma54PaperDeltaMellin D (1+I*(t:ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ((lemma54_mellin_analyticOnNhd hD hL) _ (by norm_num)).continuousAt.comp (by fun_prop)

theorem lemma54_eighth_actual_product_integrable {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (f : ℝ → ℂ) (hf : Continuous f)
    {B : ℝ} (hB : 0≤B) (hglobal : ∀t, ‖f t‖≤B) :
    Integrable (fun t : ℝ => ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖*‖f t‖) := by
  let K := lemma54EighthMomentConstant*lemma23PaperL D^7200
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg lemma54_eighth_constants_pos.2.2.2.le (pow_nonneg (by linarith) _)
  have hu := (lemma54_eighth_bounded_weight_integrable f hf hB hglobal).const_mul K
  have hcont := (lemma54_eighth_actual_line_continuous hD hL).norm.mul hf.norm
  apply hu.mono' hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  change ‖‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖*‖f t‖‖ ≤
    K*(‖f t‖*(1+t^2)^(-(4:ℤ)))
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hh := mul_le_mul_of_nonneg_right (lemma54_eighth_mellin_frequency_bound hD hL t) (norm_nonneg (f t))
  simpa only [K,zpow_neg,zpow_ofNat,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

/-- A fully integrated, actual-kernel bound. The tail amplitude B is still
explicit, to be carried through the arithmetic outer sums. -/
theorem lemma54_eighth_actual_window_and_tail {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (f : ℝ → ℂ) (hf : Continuous f)
    {B C H : ℝ} (hB : 0≤B) (hC : 0≤C) (hH : 0<H)
    (hglobal : ∀t, ‖f t‖≤B) (hwindow : ∀t, |t|≤H → ‖f t‖≤C) :
    (∫ t : ℝ, ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖*‖f t‖) ≤
      lemma54EighthMomentConstant*lemma23PaperL D^7200*(C*Real.pi+2*B/H^7) := by
  let K := lemma54EighthMomentConstant*lemma23PaperL D^7200
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg lemma54_eighth_constants_pos.2.2.2.le (pow_nonneg (by linarith) _)
  have hleft := lemma54_eighth_actual_product_integrable hD hL f hf hB hglobal
  have hright := (lemma54_eighth_bounded_weight_integrable f hf hB hglobal).const_mul K
  have hpoint (t : ℝ) : ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖*‖f t‖ ≤
      K*(‖f t‖*(1+t^2)^(-(4:ℤ))) := by
    have hh := mul_le_mul_of_nonneg_right (lemma54_eighth_mellin_frequency_bound hD hL t) (norm_nonneg (f t))
    simpa only [K,zpow_neg,zpow_ofNat,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  have hi := integral_mono_ae hleft hright (ae_of_all _ hpoint)
  rw [integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (lemma54_eighth_window_and_tail f hf hB hC hH hglobal hwindow) hK)

end ZhangLS.Spec
