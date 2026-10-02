import ZhangLS.Spec.Lemma56PrincipalMassScales
import ZhangLS.Spec.Lemma56PerronUnsmoothingScales

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_principal_mass_smoothing_parameters {L : ℝ} (hL : 10000000 ≤ L) :
    let B := Real.exp (L / 3)
    let ε := Real.exp (-L / 4)
    0 < B ∧ 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ B * ε ∧
      B ^ 2 * ε ^ 2 = Real.exp (L / 6) ∧ 2 / B ^ 2 ≤ 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hB1 := (lemma56_principal_mass_scale_parameters hL).2.2.1
  have hm : Real.exp (L / 3) * Real.exp (-L / 4) = Real.exp (L / 12) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨Real.exp_pos _, Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith only [hL0]), ?_, ?_, ?_⟩
  · rw [hm]
    exact Real.one_le_exp (by positivity)
  · rw [← mul_pow, hm, ← Real.exp_nat_mul]
    congr 1
    ring
  · have hB2 : 1 ≤ (Real.exp (L / 3)) ^ 2 := by nlinarith only [hB1]
    apply (div_le_iff₀ (sq_pos_of_pos (Real.exp_pos _))).mpr
    linarith only [hB2]

lemma lemma56_principal_mass_smoothing_polynomial {L : ℝ} (hL : 10000000 ≤ L) :
    Real.exp (-L / 4) ≤ L ^ (-200 : ℤ) ∧ L ^ 200 ≤ Real.exp (L ^ 9) := by
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have he : L ^ 200 ≤ Real.exp (L / 4) := by
    convert lemma56_principal_mass_exp_power hL 200 using 1 <;> congr 1 <;> ring
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-L / 4))
  have hcancel : Real.exp (L / 4) * Real.exp (-L / 4) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  rw [hcancel] at hm
  refine ⟨?_, ?_⟩
  · rw [zpow_neg, inv_eq_one_div]
    apply (le_div_iff₀ (pow_pos hLp 200)).mpr
    simpa only [mul_comm] using hm
  · have hL9 : L ≤ L ^ 9 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 9)
    exact he.trans (Real.exp_le_exp.mpr (by linarith only [hL9, hLp.le]))

lemma lemma56_principal_mass_near_smoothing_budget {L x : ℝ}
    (hL : 10000000 ≤ L) (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (L ^ 9)) :
    (x * (Real.exp (Real.exp (-L / 4)) - Real.exp (-(Real.exp (-L / 4)))) + 2) *
        (Real.log x + Real.exp (-L / 4)) ≤
      (12 * Real.exp 1 + 6) * Real.exp (L ^ 9) * L ^ (-191 : ℤ) := by
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hL9 : 1 ≤ L ^ 9 := by simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL1 9
  have hx0 : 0 < x := by linarith only [hx]
  have hs := lemma56_principal_mass_smoothing_parameters hL
  have hp := lemma56_principal_mass_smoothing_polynomial hL
  have hwindow := lemma56_perron_exp_window_bound hs.2.1.le hs.2.2.1
  have hlogx : Real.log x ≤ 1 + L ^ 9 := by
    have hh := Real.log_le_log hx0 hxmax
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne', Real.log_exp] at hh
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog2
    linarith only [hh, hlog2]
  have hlog : Real.log x + Real.exp (-L / 4) ≤ 3 * L ^ 9 := by
    linarith only [hlogx, hs.2.2.1, hL9]
  have hPsmall : 1 ≤ Real.exp (L ^ 9) * L ^ (-200 : ℤ) := by
    rw [zpow_neg, ← div_eq_mul_inv]
    exact (one_le_div (pow_pos hLp 200)).mpr hp.2
  have hz : L ^ (-200 : ℤ) * L ^ 9 = L ^ (-191 : ℤ) := by
    change L ^ (-200 : ℤ) * L ^ (9 : ℤ) = L ^ (-191 : ℤ)
    rw [← zpow_add₀ hLp.ne']
    norm_num
  have hwindow0 : 0 ≤ Real.exp (Real.exp (-L / 4)) - Real.exp (-(Real.exp (-L / 4))) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith only [hs.2.1]
  have hlog0 : 0 ≤ Real.log x + Real.exp (-L / 4) :=
    add_nonneg (Real.log_nonneg hx) hs.2.1.le
  have hwp := hwindow.trans (mul_le_mul_of_nonneg_left hp.1 (by positivity : 0 ≤ 2 * Real.exp 1))
  have htwo : 2 ≤ 2 * (Real.exp (L ^ 9) * L ^ (-200 : ℤ)) := by linarith only [hPsmall]
  calc
    _ ≤ (2 * Real.exp (L ^ 9) * (2 * Real.exp 1 * L ^ (-200 : ℤ)) +
        2 * (Real.exp (L ^ 9) * L ^ (-200 : ℤ))) * (3 * L ^ 9) := by
      gcongr <;> assumption
    _ = (12 * Real.exp 1 + 6) * Real.exp (L ^ 9) * (L ^ (-200 : ℤ) * L ^ 9) := by ring
    _ = _ := by rw [hz]

lemma lemma56_principal_mass_far_smoothing_margin {L : ℝ} (hL : 10000000 ≤ L) :
    4 * L ^ 9 ≤ Real.exp (L / 6) / 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hL91 : L ≤ L ^ 91 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 91)
  have hm := mul_le_mul_of_nonneg_right (by linarith only [hL91, hL] : 8 ≤ L ^ 91) (pow_nonneg hL0 9)
  rw [show L ^ 91 * L ^ 9 = L ^ 100 by ring] at hm
  have he := (lemma56_principal_mass_exp_power hL 100).trans
    (Real.exp_le_exp.mpr (by norm_num; linarith only [hL0] : (100 : ℝ) * L / 800 ≤ L / 6))
  linarith only [hm, he]

lemma lemma56_principal_mass_far_smoothing_gaussian {L : ℝ} (hL : 10000000 ≤ L) :
    Real.exp (2 / (Real.exp (L / 3)) ^ 2 -
      (Real.exp (L / 3)) ^ 2 * (Real.exp (-L / 4)) ^ 2 / 2) ≤ Real.exp (-2 * L ^ 9) := by
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hL9 : 1 ≤ L ^ 9 := by simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL1 9
  have hs := lemma56_principal_mass_smoothing_parameters hL
  have hm := lemma56_principal_mass_far_smoothing_margin hL
  apply Real.exp_le_exp.mpr
  rw [hs.2.2.2.2.1]
  linarith only [hs.2.2.2.2.2, hm, hL9]

lemma lemma56_principal_mass_far_smoothing_budget {L x : ℝ}
    (hL : 10000000 ≤ L) (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (L ^ 9)) :
    lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ * x ^ 2 *
        Real.exp (2 / (Real.exp (L / 3)) ^ 2 -
          (Real.exp (L / 3)) ^ 2 * (Real.exp (-L / 4)) ^ 2 / 2) ≤
      4 * lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ *
        Real.exp (L ^ 9) * L ^ (-191 : ℤ) := by
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hC := lemma56_gaussian_right_constant_nonneg
  have hp := (lemma56_principal_mass_smoothing_polynomial hL).2
  have hPsmall : 1 ≤ Real.exp (L ^ 9) * L ^ (-200 : ℤ) := by
    rw [zpow_neg, ← div_eq_mul_inv]
    exact (one_le_div (pow_pos hLp 200)).mpr hp
  have hP191 : 1 ≤ Real.exp (L ^ 9) * L ^ (-191 : ℤ) := hPsmall.trans
    (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hL1 (by norm_num : (-200 : ℤ) ≤ -191)) (Real.exp_nonneg _))
  have hg := lemma56_principal_mass_far_smoothing_gaussian hL
  have hx0 : 0 ≤ x := by linarith only [hx]
  have heq : (Real.exp (L ^ 9)) ^ 2 * Real.exp (-2 * L ^ 9) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  calc
    _ ≤ lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ *
        (2 * Real.exp (L ^ 9)) ^ 2 * Real.exp (-2 * L ^ 9) := by gcongr
    _ = 4 * lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ := by
      rw [mul_pow]
      calc
        _ = (4 * lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹) *
            ((Real.exp (L ^ 9)) ^ 2 * Real.exp (-2 * L ^ 9)) := by ring
        _ = _ := by rw [heq, mul_one]
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hP191
        (by positivity : 0 ≤ 4 * lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹) using 1 <;> ring

noncomputable def lemma56PrincipalUnsmoothingConstant : ℝ :=
  12 * Real.exp 1 + 6 + 4 * lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹

lemma lemma56_principal_unsmoothing_constant_pos : 0 < lemma56PrincipalUnsmoothingConstant := by
  have hC := lemma56_gaussian_right_constant_nonneg
  dsimp [lemma56PrincipalUnsmoothingConstant]
  positivity

lemma lemma56_actual_principal_mass_smoothing_removal {D q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hL : 10000000 ≤ lemma23PaperL D)
    {x : ℝ} (hx : 1 ≤ x) (hxmax : x ≤ 2 * lemma23PaperP D) (τ : ℝ) :
    ‖lemma56PerronMangoldtSum θ (Real.exp (lemma23PaperL D / 3)) x τ -
      lemma56SharpMangoldtSum θ x τ‖ ≤
      lemma56PrincipalUnsmoothingConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  have hs := lemma56_principal_mass_smoothing_parameters hL
  have hb := lemma56_actual_perron_smoothing_error_bound θ hs.1 hx hs.2.1.le hs.2.2.2.1 τ
  have hn := lemma56_principal_mass_near_smoothing_budget hL hx hxmax
  have hf := lemma56_principal_mass_far_smoothing_budget hL hx hxmax
  apply hb.trans
  dsimp [lemma56PrincipalUnsmoothingConstant, lemma23PaperP]
  linarith only [hn, hf]

end ZhangLS.Spec
