import ZhangLS.Spec.Proposition141GlobalShift

/-! # Explicit rates for genuine Section14 large-index tails

At the already fixed ℒ≥2000 threshold, the actual exp(−ℒ¹⁰/2) envelope
absorbs every P-power up to P^500 and still leaves D^−100. These are bounds
on the actual paper parameters, not an undefined α₁ assigned to an error.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec

lemma proposition141_large_tail_prime_power_absorption {L : ℝ} (hL : 2000≤L)
    (m : ℕ) (hm : m≤500) :
    Real.exp (-L^10/2)*(Real.exp (L^9))^m≤Real.exp (-L^10/4) := by
  have hLp : 0≤L := by linarith
  have hmR : (m:ℝ)≤500 := by exact_mod_cast hm
  have hb : (m:ℝ)*L^9≤L^10/4 := by
    calc
      _ ≤ (L/4)*L^9 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hLp _)
      _ = _ := by ring
  rw [←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Fixed, fully quantitative rate for the actual prime scale. -/
theorem proposition141_actual_tail_prime_power_absorption {D : ℕ}
    (hL : 2000≤lemma23PaperL D) (m : ℕ) (hm : m≤500) :
    Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^m≤
      Real.exp (-lemma23PaperL D^10/4) :=
  proposition141_large_tail_prime_power_absorption hL m hm

/-- The remaining tail is already much smaller than a fixed negative
power of D at the same explicit threshold. -/
theorem proposition141_actual_large_tail_decay {D : ℕ} (hD : 0<D)
    (hL : 2000≤lemma23PaperL D) :
    Real.exp (-lemma23PaperL D^10/4)≤1/(D:ℝ)^100 := by
  have hDp : 0<(D:ℝ) := by exact_mod_cast hD
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hL0 : 0≤lemma23PaperL D := by linarith
  have hpow : 400≤lemma23PaperL D^9 := by
    have hh : lemma23PaperL D≤lemma23PaperL D^9 := le_self_pow₀ hL1 (by norm_num)
    linarith
  have hb : 100*lemma23PaperL D≤lemma23PaperL D^10/4 := by
    have hh := mul_le_mul_of_nonneg_right hpow hL0
    nlinarith [show lemma23PaperL D^9*lemma23PaperL D=lemma23PaperL D^10 by ring]
  calc
    _ ≤ Real.exp (-(100*lemma23PaperL D)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_neg,show (100:ℝ)=(100:ℕ) by norm_num,Real.exp_nat_mul]
      simp only [lemma23PaperL,Real.exp_log hDp,one_div]

/-- Actual exponential large-index errors tolerate the whole retained
polynomial prime-scale budget before tending to zero uniformly. -/
theorem proposition141_actual_tail_polynomial_rate {D : ℕ} (hD : 0<D)
    (hL : 2000≤lemma23PaperL D) (m : ℕ) (hm : m≤500) :
    Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^m≤1/(D:ℝ)^100 :=
  (proposition141_actual_tail_prime_power_absorption hL m hm).trans
    (proposition141_actual_large_tail_decay hD hL)

end ZhangLS.Spec
