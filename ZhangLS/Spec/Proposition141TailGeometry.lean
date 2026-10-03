import ZhangLS.Spec.TauWeightedDeltaGeometry
import ZhangLS.Spec.Proposition141GlobalShift

/-! # Explicit actual geometry for the full P³ long-index cutoff -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec

lemma proposition141_log_scale_le_P {D:ℕ} (hL:2000≤lemma23PaperL D) :
    2*lemma23PaperL D^530≤lemma23PaperP D := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hL8 : 531≤lemma23PaperL D^8 := by
    have hh := le_self_pow₀ hL1 (by norm_num : 8≠0)
    linarith
  have hlog : 531*Real.log (lemma23PaperL D)≤lemma23PaperL D^9 := by
    have hh := mul_le_mul_of_nonneg_right hL8 hLp.le
    have hl := Real.log_le_sub_one_of_pos hLp
    calc
      _≤531*lemma23PaperL D := by linarith
      _≤lemma23PaperL D^8*lemma23PaperL D := hh
      _=_ := by ring
  calc
    _≤lemma23PaperL D*lemma23PaperL D^530 :=
      mul_le_mul_of_nonneg_right (by linarith : (2:ℝ)≤lemma23PaperL D) (pow_nonneg hLp.le _)
    _=lemma23PaperL D^531 := by ring
    _=Real.exp (531*Real.log (lemma23PaperL D)) := by rw [show (531:ℝ)=(531:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hLp]
    _≤_ := Real.exp_le_exp.mpr hlog

lemma proposition141_actual_P_cube_tail_cutoff {D:ℕ} (hL:2000≤lemma23PaperL D)
    {h r:ℝ} (_hh:0≤h) (_hr:0≤r) (hhr:h*r≤lemma23PaperP D) :
    (2*lemma23PaperP D*h*r)*lemma51PaperT0 D^(51/50:ℝ)≤lemma23PaperP D^3 := by
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have ht : 0≤lemma51PaperT0 D^(51/50:ℝ) := Real.rpow_nonneg
    (pow_nonneg (by linarith : 0≤lemma23PaperL D) _) _
  calc
    _≤(2*lemma23PaperP D*lemma23PaperP D)*lemma23PaperL D^530 := by
      have hh' := mul_le_mul_of_nonneg_left hhr (show 0≤2*lemma23PaperP D by positivity)
      have hb := mul_le_mul hh' (tauDelta_t0_cutoff (by linarith : 1≤lemma23PaperL D)) ht (by positivity)
      simpa only [mul_assoc] using hb
    _=lemma23PaperP D^2*(2*lemma23PaperL D^530) := by ring
    _≤lemma23PaperP D^2*lemma23PaperP D := mul_le_mul_of_nonneg_left (proposition141_log_scale_le_P hL) (sq_nonneg _)
    _=_ := by ring

end ZhangLS.Spec
