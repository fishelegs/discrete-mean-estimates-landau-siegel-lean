import ZhangLS.Spec.Proposition141NormalizedLargeAggregate
import ZhangLS.Spec.Proposition141ConductorBudget

/-! # Explicit rates for the original D³ small-conductor boundary -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec

lemma proposition141_decay_le_inverse_seventh {D:ℕ} (hD:0<D)
    (hL:2000≤lemma23PaperL D) : lemma56Decay D≤(D:ℝ)^(-(7:ℤ)) := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hL0 : 0≤lemma23PaperL D := by linarith
  have hpow : (lemma23PaperL D)^2≤lemma23PaperL D^(9/2:ℝ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (2:ℝ)≤9/2)
  have hp : 7*lemma23PaperL D≤lemma23PaperL D^(9/2:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show (7:ℝ)≤lemma23PaperL D by linarith) hL0
    have hh' : 7*lemma23PaperL D≤lemma23PaperL D^2 := by simpa only [pow_two] using hh
    exact hh'.trans hpow
  have hDp : 0<(D:ℝ) := by exact_mod_cast hD
  calc
    _≤Real.exp (-(7*lemma23PaperL D)) := Real.exp_le_exp.mpr (neg_le_neg hp)
    _=_ := by
      rw [Real.exp_neg,show (7:ℝ)=(7:ℕ) by norm_num,Real.exp_nat_mul]
      simp only [lemma23PaperL,Real.exp_log hDp,zpow_neg,zpow_ofNat]

lemma proposition141_small_normalized_scalar {D:ℕ} (hD:0<D)
    (hL:2000≤lemma23PaperL D) :
    (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*((D^3:ℕ):ℝ)^(3/2:ℝ)*(D:ℝ)/Real.sqrt (D:ℝ)≤
      2/(D:ℝ)^2 := by
  have hDp : 0<(D:ℝ) := by exact_mod_cast hD
  have hs : lemma56Decay D+(D:ℝ)^(-(7:ℤ))≤2*(D:ℝ)^(-(7:ℤ)) := by
    linarith [proposition141_decay_le_inverse_seventh hD hL]
  calc
    _≤(2*(D:ℝ)^(-(7:ℤ)))*((D^3:ℕ):ℝ)^(3/2:ℝ)*(D:ℝ)/Real.sqrt (D:ℝ) := by gcongr
    _=2*((((D:ℝ)*((D:ℝ)^3)^(3/2:ℝ)/(D:ℝ)^7)/Real.sqrt (D:ℝ))) := by
      simp only [Nat.cast_pow,zpow_neg,zpow_ofNat]
      ring
    _=_ := by
      rw [proposition141_eighth_gauss_tail_identity hDp,Real.rpow_neg hDp.le,Real.rpow_two]
      ring

lemma proposition141_floor_P_cube_log_five {D:ℕ} (hL:1≤lemma23PaperL D) :
    1≤⌊lemma23PaperP D^3⌋₊ ∧
      (1+Real.log (⌊lemma23PaperP D^3⌋₊:ℝ))^5≤1024*lemma23PaperL D^45 := by
  have hL9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp (by positivity)
  have hY : 1≤⌊lemma23PaperP D^3⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_pow₀ hP1 (n:=3))
  refine ⟨hY,?_⟩
  have hYp : 0<(⌊lemma23PaperP D^3⌋₊:ℝ) := by exact_mod_cast (show 0<⌊lemma23PaperP D^3⌋₊ by omega)
  have hYP : (⌊lemma23PaperP D^3⌋₊:ℝ)≤lemma23PaperP D^3 := Nat.floor_le (by positivity)
  have hlog : Real.log (⌊lemma23PaperP D^3⌋₊:ℝ)≤3*lemma23PaperL D^9 := by
    simpa only [Real.log_pow,lemma23PaperP,Real.log_exp,Nat.cast_ofNat] using Real.log_le_log hYp hYP
  have hb : 1+Real.log (⌊lemma23PaperP D^3⌋₊:ℝ)≤4*lemma23PaperL D^9 := by linarith
  calc
    _≤(4*lemma23PaperL D^9)^5 := pow_le_pow_left₀ (by have := Real.log_natCast_nonneg ⌊lemma23PaperP D^3⌋₊; positivity) hb 5
    _=_ := by ring

lemma proposition141_small_log_budget {D:ℕ} (hL:1≤lemma23PaperL D) :
    lemma23PaperL D^7200*(1+Real.log (⌊lemma23PaperP D^3⌋₊:ℝ))^5*
      (1+Real.log (⌊lemma23PaperP D⌋₊:ℝ))^7*(1+Real.log (D:ℝ))^5 ≤
      4194304*lemma23PaperL D^7313 := by
  have hX := (proposition141_floor_P_log_seven hL).2
  have hY := (proposition141_floor_P_cube_log_five hL).2
  have hDlog : (1+Real.log (D:ℝ))^5≤32*lemma23PaperL D^5 := by
    have hb : 1+Real.log (D:ℝ)≤2*lemma23PaperL D := by change 1+lemma23PaperL D≤_; linarith
    calc
      _≤(2*lemma23PaperL D)^5 := pow_le_pow_left₀ (by have := Real.log_natCast_nonneg D; positivity) hb 5
      _=_ := by ring
  calc
    _≤lemma23PaperL D^7200*(1024*lemma23PaperL D^45)*(128*lemma23PaperL D^63)*(32*lemma23PaperL D^5) := by
      gcongr
    _=_ := by ring

end ZhangLS.Spec
