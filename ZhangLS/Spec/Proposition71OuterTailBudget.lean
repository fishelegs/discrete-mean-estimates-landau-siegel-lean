import ZhangLS.Spec.Proposition71OffLocalAggregate

/-! # An explicit scalar budget for all small-truncation tail weights -/
set_option autoImplicit false
namespace ZhangLS.Spec
set_option maxHeartbeats 2000000

lemma proposition71_outer_tail_budget {D X Q : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hX : 1≤X)
    (hXP : (X : ℝ)≤lemma23PaperP D) (hQP : (Q : ℝ)≤lemma23PaperP D) :
    lemma23PaperP D^2*Real.exp (-lemma23PaperL D^10/2)*
      (Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7≤2^7*(D : ℝ)⁻¹ := by
  have hLp : 0≤lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg hLp 9)
  have hQ2 : (Q : ℝ)^(3/2 : ℝ)≤lemma23PaperP D^2 := by
    calc
      _≤lemma23PaperP D^(3/2 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg Q) hQP (by norm_num)
      _≤lemma23PaperP D^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
      _=_ := Real.rpow_two _
  have hlog : Real.log (X : ℝ)≤lemma23PaperL D^9 := by
    have hh := Real.log_le_log (by exact_mod_cast hX : (0:ℝ)<X) hXP
    simpa [lemma23PaperP] using hh
  have hlog0 : 0≤1+Real.log (X : ℝ) := by have := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X); linarith
  have hlog7 : (1+Real.log (X : ℝ))^7≤2^7*lemma23PaperL D^63 := by
    have h9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL1
    have hh := pow_le_pow_left₀ hlog0 (show 1+Real.log (X : ℝ)≤2*lemma23PaperL D^9 by linarith) 7
    simpa only [mul_pow,←pow_mul] using hh
  calc
    _≤lemma23PaperP D^2*Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^2*(2^7*lemma23PaperL D^63) := by gcongr
    _=2^7*(lemma23PaperP D^4*lemma23PaperL D^63*Real.exp (-lemma23PaperL D^10/2)) := by ring
    _≤2^7*(lemma23PaperP D^6*lemma23PaperL D^72*Real.exp (-lemma23PaperL D^10/2)) := by
      have hp46 : lemma23PaperP D^4≤lemma23PaperP D^6 := pow_le_pow_right₀ hP1 (by norm_num)
      have hl6372 : lemma23PaperL D^63≤lemma23PaperL D^72 := pow_le_pow_right₀ hL1 (by norm_num)
      gcongr
    _≤_ := mul_le_mul_of_nonneg_left (proposition71_tail_scalar_budget hD hL) (by positivity)

end ZhangLS.Spec
