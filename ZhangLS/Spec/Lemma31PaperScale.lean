import ZhangLS.Spec.Lemma31LinearTail
import ZhangLS.Spec.Lemma23GoodSet
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset MeasureTheory Set
set_option maxHeartbeats 2000000

noncomputable def lemma31PaperCutoff (D : ℕ) : ℕ := ⌊lemma23PaperP D^2⌋₊

lemma lemma31_D_le_P {D : ℕ} (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) :
    (D : ℝ) ≤ lemma23PaperP D := by
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hp : lemma23PaperL D ≤ lemma23PaperL D^9 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (show (1 : ℕ) ≤ 9 by norm_num)
  calc
    _ = Real.exp (lemma23PaperL D) := (Real.exp_log hd).symm
    _ ≤ _ := Real.exp_le_exp.mpr hp

lemma lemma31_D_square_le_paper_cutoff {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) : D^2 ≤ lemma31PaperCutoff D := by
  apply (Nat.le_floor_iff (sq_nonneg (lemma23PaperP D))).mpr
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg D) (lemma31_D_le_P hD hL) 2
  simpa only [Nat.cast_pow] using hp

lemma lemma31_paper_cutoff_log_le {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) :
    Real.log (lemma31PaperCutoff D : ℝ) ≤ 2*lemma23PaperL D^9 := by
  have hc := lemma31_D_square_le_paper_cutoff hD hL
  have hn : (0 : ℝ) < lemma31PaperCutoff D := by
    have hp : 0 < D^2 := pow_pos (show 0 < D by omega) 2
    exact_mod_cast hp.trans_le hc
  have hf : (lemma31PaperCutoff D : ℝ) ≤ lemma23PaperP D^2 := Nat.floor_le (sq_nonneg _)
  have hh := Real.log_le_log hn hf
  simpa only [Real.log_pow,lemma23PaperP,Real.log_exp] using hh

lemma lemma31_paper_cutoff_log_factor_le {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) :
    1+Real.log (lemma31PaperCutoff D : ℝ) ≤ 3*lemma23PaperL D^9 := by
  have hp : 1 ≤ lemma23PaperL D^9 := one_le_pow₀ hL
  have hh := lemma31_paper_cutoff_log_le hD hL
  linarith

end ZhangLS.Spec
