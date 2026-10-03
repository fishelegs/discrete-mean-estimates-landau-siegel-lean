import ZhangLS.Spec.LogMomentUniform

/-! The second jet is constrained by the genuine nonnegative first moment. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec

/-- Exact identity retaining the genuine nonnegative moment and its proved
source error; the curvature ratio is not an independently selectable parameter. -/
lemma lemma171_actual_curvature_moment_identity {D : ℕ}
    (χ : RealPrimitiveCharacter D) (ha : lemma171MainTerm χ ≠ 0) :
    lemma171RealSecondJet χ / realLDerivAtOne χ =
      -lemma171FirstLogMoment χ / (2 * lemma171MainTerm χ) -
        Real.eulerMascheroniConstant - lemma171CorrectionLogDerivative D / 2 +
        lemma171FirstLogMomentError χ / (2 * lemma171MainTerm χ) := by
  unfold lemma171FirstLogMomentError
  rw [show 2 * lemma171RealSecondJet χ / realLDerivAtOne χ =
    2 * (lemma171RealSecondJet χ / realLDerivAtOne χ) by ring]
  generalize hquot : lemma171RealSecondJet χ / realLDerivAtOne χ = q
  field_simp [ha]
  <;> ring

lemma lemma171_actual_curvature_moment_constraint {D : ℕ}
    (χ : RealPrimitiveCharacter D) (ha : 0 < lemma171MainTerm χ) :
    -(4 * lemma23PaperL D * lemma171ShortHarmonicSum χ + |lemma171FirstLogMomentError χ|) /
        lemma171MainTerm χ ≤
      2 * lemma171RealSecondJet χ / realLDerivAtOne χ +
        2 * Real.eulerMascheroniConstant + lemma171CorrectionLogDerivative D ∧
    2 * lemma171RealSecondJet χ / realLDerivAtOne χ +
        2 * Real.eulerMascheroniConstant + lemma171CorrectionLogDerivative D ≤
      |lemma171FirstLogMomentError χ| / lemma171MainTerm χ := by
  have hm0 := lemma171_first_log_moment_nonneg χ
  have hm1 := lemma171_first_log_moment_le χ
  have he0 := neg_abs_le (lemma171FirstLogMomentError χ)
  have he1 := le_abs_self (lemma171FirstLogMomentError χ)
  unfold lemma171FirstLogMomentError at he0 he1
  unfold lemma171FirstLogMomentError
  constructor
  · apply (div_le_iff₀ ha).mpr
    nlinarith
  · apply (le_div_iff₀ ha).mpr
    nlinarith

lemma lemma171_loglog_square_le_linear {L : ℝ} (hL : 1 ≤ L) :
    (1 + Real.log L)^2 ≤ 9 * L := by
  have hL0 : 0 ≤ L := by linarith
  have hlog0 := Real.log_nonneg hL
  have hlog := Real.log_le_rpow_div hL0 (by norm_num : (0 : ℝ) < 1/2)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hs := Real.sq_sqrt hL0
  have hs1 : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hs0 := Real.sqrt_nonneg L
  have hsq : (1 + Real.log L)^2 ≤ (3 * Real.sqrt L)^2 := by
    apply pow_le_pow_left₀ (by linarith)
    linarith
  nlinarith

noncomputable def lemma171CurvatureConstant : ℝ :=
  10 + |2 * Real.eulerMascheroniConstant| + 9 * lemma171CorrectionLogDerivativeBound

lemma lemma171_curvature_constant_pos : 0 < lemma171CurvatureConstant := by
  have hJ := lemma171_correction_log_derivative_bound_pos
  unfold lemma171CurvatureConstant
  positivity

/-- The actual ratio e/d is O(log D), uniformly under the original (A). -/
theorem lemma171_actual_curvature_uniform :
    ∃ D₀ : ℕ, 3 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        |lemma171RealSecondJet χ / realLDerivAtOne χ| ≤
          lemma171CurvatureConstant * lemma23PaperL D := by
  obtain ⟨D₁, _, hmain⟩ := lemma171_actual_main_gt_half
  obtain ⟨D₂, _, hmoment⟩ := lemma171_actual_first_log_moment_uniform (1/2) (by norm_num)
  obtain ⟨D₃, _, hsum⟩ := lemma171_proved (1/2) (by norm_num)
  refine ⟨max 3 (max D₁ (max D₂ D₃)), le_max_left _ _, ?_⟩
  intro D hD χ hA
  have h3 : 3 ≤ D := (le_max_left _ _).trans hD
  have hr := (le_max_right _ _).trans hD
  have hd1 : D₁ ≤ D := (le_max_left _ _).trans hr
  have hr' := (le_max_right _ _).trans hr
  have hd2 : D₂ ≤ D := (le_max_left _ _).trans hr'
  have hd3 : D₃ ≤ D := (le_max_right _ _).trans hr'
  have ha := hmain D hd1 χ hA
  have ha0 : 0 < lemma171MainTerm χ := by linarith
  have he := hmoment D hd2 χ hA
  have hs := hsum D hd3 χ hA
  unfold lemma171Error at hs
  have hS : lemma171ShortHarmonicSum χ ≤ 2 * lemma171MainTerm χ := by
    have hh := (abs_lt.mp hs).2
    linarith only [hh, ha]
  have hL : 1 ≤ lemma23PaperL D := (lemma83_log_nat_gt_one h3).le
  have hL0 : 0 ≤ lemma23PaperL D := by linarith only [hL]
  have hM0 := lemma171_first_log_moment_nonneg χ
  have hMle := lemma171_first_log_moment_le χ
  have hM : lemma171FirstLogMoment χ ≤ 8 * lemma23PaperL D * lemma171MainTerm χ := by
    have hh := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 4 * lemma23PaperL D)
    nlinarith only [hh, hMle]
  have hE := abs_lt.mp he
  unfold lemma171FirstLogMomentError at hE
  have hKlo : -8 * lemma23PaperL D - 1 ≤
      2 * lemma171RealSecondJet χ / realLDerivAtOne χ +
        2 * Real.eulerMascheroniConstant + lemma171CorrectionLogDerivative D := by
    apply (mul_le_mul_iff_left₀ ha0).mp
    nlinarith only [ha, hM, hE.1]
  have hKhi : 2 * lemma171RealSecondJet χ / realLDerivAtOne χ +
      2 * Real.eulerMascheroniConstant + lemma171CorrectionLogDerivative D ≤ 1 := by
    apply (mul_le_mul_iff_left₀ ha0).mp
    nlinarith only [ha, hM0, hE.2]
  have hJ : |lemma171CorrectionLogDerivative D| ≤
      9 * lemma171CorrectionLogDerivativeBound * lemma23PaperL D := by
    have hh := lemma171_correction_log_derivative_abs_le D h3
    have hll := lemma171_loglog_square_le_linear hL
    have hJ0 := lemma171_correction_log_derivative_bound_pos.le
    have hm := mul_le_mul_of_nonneg_left hll hJ0
    exact hh.trans (by simpa only [lemma23PaperL, mul_assoc, mul_comm, mul_left_comm] using hm)
  have hJtwo := abs_le.mp hJ
  have hγ := abs_le.mp (le_refl |2 * Real.eulerMascheroniConstant|)
  have hγscale := mul_le_mul_of_nonneg_left hL (abs_nonneg (2 * Real.eulerMascheroniConstant))
  apply abs_le.mpr
  unfold lemma171CurvatureConstant
  have hratio : 2 * lemma171RealSecondJet χ / realLDerivAtOne χ =
      2 * (lemma171RealSecondJet χ / realLDerivAtOne χ) := by ring
  rw [hratio] at hKlo hKhi
  constructor <;> nlinarith only [hKlo, hKhi, hJtwo.1, hJtwo.2,
    hγ.1, hγ.2, hγscale, hL]

/-- Division by log P=L^9 exposes the improved, actual L^-8 curvature scale. -/
theorem lemma171_actual_normalized_curvature_uniform :
    ∃ D₀ : ℕ, 3 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        |lemma171RealSecondJet χ / (realLDerivAtOne χ * Real.log (lemma23PaperP D))| ≤
          lemma171CurvatureConstant * lemma23PaperL D ^ (-8 : ℤ) := by
  obtain ⟨D₀, hD₀, hbound⟩ := lemma171_actual_curvature_uniform
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD χ hA
  have hL : 0 < lemma23PaperL D := (lemma83_log_nat_gt_one (hD₀.trans hD)).trans' (by norm_num)
  have hh := hbound D hD χ hA
  rw [lemma23PaperP, Real.log_exp, ← div_div, abs_div, abs_of_pos (pow_pos hL 9)]
  calc
    _ ≤ (lemma171CurvatureConstant * lemma23PaperL D) / lemma23PaperL D ^ 9 :=
      div_le_div_of_nonneg_right hh (pow_nonneg hL.le _)
    _ = _ := by
      rw [zpow_neg, zpow_ofNat]
      field_simp [hL.ne']
      <;> ring

end ZhangLS.Spec
