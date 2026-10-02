import ZhangLS.Spec.Lemma54UniformSecondMoment
import ZhangLS.Spec.Lemma54DiskErrorAbsorption

/-! # The complete faithful original target of Lemma 5.4

The actual transform and its full right-half-plane analyticity, actual
first/second derivative formulas, their weighted tails, all endpoint limits,
and two Mellin integrations by parts are proved. The actual second moment
is uniformly at most C L^3200 on the full closed strip, proving the first
original estimate with one absolute constant and one natural modulus threshold.
The actual Gaussian normalization, all positive-axis exterior pieces,
polynomial-exponential error absorption and common constants are proved.
The theorem below retains the full original closed strip, the full original
open disk, and one common absolute constant and natural modulus threshold.
-/

namespace ZhangLS.Spec

open Complex

def Lemma54AtConstants (C c : ℝ) (D₀ : ℕ) : Prop :=
  ∀ D : ℕ, D₀ ≤ D →
    AnalyticOnNhd ℂ (lemma54PaperDeltaMellin D) {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
        ‖lemma54PaperDeltaMellin D s‖ ≤ C * lemma23PaperL D ^ c / ‖s‖ ^ 2) ∧
      (∀ s : ℂ, ‖s - 1‖ < 10 * lemma44PaperAlpha D →
        ‖lemma54PaperDeltaMellin D s - 1‖ ≤
          C * lemma44PaperAlpha D * Real.log (lemma23PaperL D))

def Lemma54Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, Lemma54AtConstants C c D₀

noncomputable def lemma54Constant : ℝ := lemma54MellinStripConstant + lemma54DiskConstant

theorem lemma54_constant_pos : 0 < lemma54Constant :=
  add_pos lemma54_mellin_strip_constant_pos lemma54_disk_constant_pos

theorem lemma54_uniform_constants : ∃ D₀ : ℕ, Lemma54AtConstants lemma54Constant 3200 D₀ := by
  obtain ⟨D₀, hD₀⟩ := lemma54_actual_mellin_disk_uniform_threshold
  refine ⟨D₀, ?_⟩
  intro D hD
  have ht := hD₀ D hD
  have hL0 : 0 ≤ lemma23PaperL D := by linarith [ht.2.1]
  have hCM : lemma54MellinStripConstant ≤ lemma54Constant := by
    unfold lemma54Constant
    linarith [lemma54_disk_constant_pos]
  have hCD : lemma54DiskConstant ≤ lemma54Constant := by
    unfold lemma54Constant
    linarith [lemma54_mellin_strip_constant_pos]
  refine ⟨lemma54_mellin_analyticOnNhd ht.1 ht.2.1, ?_, ?_⟩
  · intro s hs hs2
    apply (lemma54_actual_mellin_closed_strip_bound ht.1 ht.2.1 hs hs2).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCM (Real.rpow_nonneg hL0 (3200 : ℝ))) (sq_nonneg ‖s‖)
  · intro s hs
    apply (ht.2.2 s hs).trans
    have hα := (lemma54_disk_alpha_small ht.2.1).1
    have hlog := Real.log_nonneg (show 1 ≤ lemma23PaperL D by linarith [ht.2.1])
    have hh := mul_le_mul_of_nonneg_right hCD (mul_nonneg hα.le hlog)
    simpa only [mul_assoc] using hh

theorem lemma54_proved : Lemma54Target :=
  ⟨lemma54Constant, lemma54_constant_pos, 3200, by norm_num, lemma54_uniform_constants⟩

end ZhangLS.Spec
