import ZhangLS.Spec.FixedHProfileWindow
import ZhangLS.Spec.CharacterPeriodSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The actual chi-weighted fixed-H sequence, with h(0)=0. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHProfile
open Set Function
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def h {D : ℕ} (χ : RealPrimitiveCharacter D) (P : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ.evalNat n * (f (Real.log n / Real.log P) : ℂ)

lemma h_zero {D : ℕ} (χ : RealPrimitiveCharacter D) (P : ℝ) : h χ P 0 = 0 := by
  simp [h]

lemma h_eq_of_pos {D n : ℕ} (χ : RealPrimitiveCharacter D) (P : ℝ) (hn : 0 < n) :
    h χ P n = χ.evalNat n * (f (Real.log n / Real.log P) : ℂ) := by
  simp [h, hn.ne']

lemma h_norm_le_one {D : ℕ} (χ : RealPrimitiveCharacter D) (P : ℝ) (n : ℕ) :
    ‖h χ P n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [h, hn]
  · rw [h, if_neg hn, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul (χ.evalNat_norm_le_one n) (f_abs_le_one _)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

lemma h_support_window {D n : ℕ} (χ : RealPrimitiveCharacter D) {P : ℝ} (hP : 1 < P)
    (hn : h χ P n ≠ 0) :
    0 < n ∧ Real.exp ((251 / 500) * Real.log P) < (n : ℝ) ∧
      (n : ℝ) < Real.exp ((201 / 400) * Real.log P) := by
  have hn0 : n ≠ 0 := by intro hz; exact hn (hz ▸ h_zero χ P)
  have hnp : 0 < n := Nat.pos_of_ne_zero hn0
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hnp
  have hf : f (Real.log n / Real.log P) ≠ 0 := by
    intro hz
    exact hn (by simp [h, hz, hn0])
  have hw := f_support hf
  have hB : 0 < Real.log P := Real.log_pos hP
  have hlo : (251 / 500) * Real.log P < Real.log n := (lt_div_iff₀ hB).mp hw.1
  have hhi : Real.log n < (201 / 400) * Real.log P := (div_lt_iff₀ hB).mp hw.2
  refine ⟨hnp, ?_, ?_⟩
  · simpa only [Real.exp_log hnr] using Real.exp_lt_exp.mpr hlo
  · simpa only [Real.exp_log hnr] using Real.exp_lt_exp.mpr hhi

lemma h_eq_zero_of_below {D n : ℕ} (χ : RealPrimitiveCharacter D) {P : ℝ} (hP : 1 < P)
    (hn : (n : ℝ) ≤ Real.exp ((251 / 500) * Real.log P)) : h χ P n = 0 := by
  by_contra hz
  exact (not_lt_of_ge hn) (h_support_window χ hP hz).2.1

lemma h_support_rpow {D n : ℕ} (χ : RealPrimitiveCharacter D) {P : ℝ} (hP : 1 < P)
    (hn : h χ P n ≠ 0) :
    P ^ (251 / 500 : ℝ) < (n : ℝ) ∧ (n : ℝ) < P ^ (201 / 400 : ℝ) := by
  simpa only [Real.rpow_def_of_pos (by linarith : 0 < P), mul_comm] using
    (h_support_window χ hP hn).2

lemma h_eq_zero_of_above {D n : ℕ} (χ : RealPrimitiveCharacter D) {P : ℝ} (hP : 1 < P)
    (hn : Real.exp ((201 / 400) * Real.log P) ≤ (n : ℝ)) : h χ P n = 0 := by
  by_contra hz
  exact (not_lt_of_ge hn) (h_support_window χ hP hz).2.2

lemma h_support_finite {D : ℕ} (χ : RealPrimitiveCharacter D) {P : ℝ} (hP : 1 < P) :
    (Function.support (h χ P)).Finite := by
  apply (Set.finite_Icc 1 ⌊Real.exp ((201 / 400) * Real.log P)⌋₊).subset
  intro n hn
  have hw := h_support_window χ hP hn
  exact ⟨hw.1, Nat.le_floor hw.2.2.le⟩

end ZhangLS.Spec.FixedHProfile
