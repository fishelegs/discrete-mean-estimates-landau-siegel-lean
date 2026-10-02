import ZhangLS.Spec.Lemma81PrincipalPerron
import ZhangLS.Spec.Lemma56PrincipalMassContourBudget
import ZhangLS.Spec.Lemma56PrincipalMassUnsmoothing

/-! # Fixed paper-scale budgets for the unconditional principal Perron route -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma81_principal_mass_moment_budget {L : ℝ} (hL : 10000000 ≤ L) :
    0 ≤ 360000000 * L ^ 2 + 20021600 * L ∧
      360000000 * L ^ 2 + 20021600 * L ≤ 380021600 * L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hm := mul_le_mul_of_nonneg_right hL1 hL0
  exact ⟨by positivity, by nlinarith only [hm]⟩

lemma lemma81_principal_mass_left_power {L : ℝ} (hL : 0 < L) :
    (Real.exp (L ^ 9)) ^ (1 - 1 / (20000000 * L)) = Real.exp (L ^ 9 - L ^ 8 / 20000000) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp [hL.ne']

lemma lemma81_principal_mass_left_budget {L x : ℝ} (hL : 10000000 ≤ L)
    (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (L ^ 9)) :
    6 * (360000000 * L ^ 2 + 20021600 * L) * x ^ (1 - 1 / (20000000 * L)) *
      Real.exp ((1 - 1 / (20000000 * L)) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) *
        Real.log (1 + Real.exp L / 2) ≤
      4560259200 * Real.exp 1 * Real.exp (L ^ 9) * L ^ 3 * Real.exp (-(L ^ 8 / 20000000)) := by
  have hLp : 0 < L := by linarith only [hL]
  have hL0 : 0 ≤ L := hLp.le
  have hs := lemma56_principal_mass_scale_parameters hL
  have ha0 : 0 ≤ 1 - 1 / (20000000 * L) := by
    have hsmall : 1 / (20000000 * L) ≤ (1 / 2 : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 20000000 * L) (by norm_num)).mpr
      linarith only [hL]
    linarith only [hsmall]
  have ha1 : 1 - 1 / (20000000 * L) ≤ 1 := sub_le_self _ (by positivity)
  have hM := (lemma81_principal_mass_moment_budget hL).2
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hP : 0 < Real.exp (L ^ 9) := Real.exp_pos _
  have hpow : x ^ (1 - 1 / (20000000 * L)) ≤
      2 * Real.exp (L ^ 9) * Real.exp (-(L ^ 8 / 20000000)) := by
    have htwo : (2 : ℝ) ^ (1 - 1 / (20000000 * L)) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
    calc
      _ ≤ (2 * Real.exp (L ^ 9)) ^ (1 - 1 / (20000000 * L)) := Real.rpow_le_rpow hx0 hxmax ha0
      _ = (2 : ℝ) ^ (1 - 1 / (20000000 * L)) * (Real.exp (L ^ 9)) ^ (1 - 1 / (20000000 * L)) :=
        Real.mul_rpow (by norm_num) hP.le
      _ ≤ 2 * (Real.exp (L ^ 9)) ^ (1 - 1 / (20000000 * L)) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hP.le _)
      _ = _ := by
        rw [lemma81_principal_mass_left_power hLp]
        rw [show Real.exp (L ^ 9 - L ^ 8 / 20000000) = Real.exp (L ^ 9) * Real.exp (-(L ^ 8 / 20000000)) by
          rw [← Real.exp_add]; congr 1]
        ring
  have ha2 : (1 - 1 / (20000000 * L)) ^ 2 ≤ 1 := by nlinarith only [ha0, ha1]
  have hB2 : 1 ≤ (Real.exp (L / 3)) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs.2.2.1 2
    simpa only [one_pow] using hh
  have hex : Real.exp ((1 - 1 / (20000000 * L)) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_one (by positivity : 0 < 4 * (Real.exp (L / 3)) ^ 2)).mpr
    linarith only [ha2, hB2]
  have hlog : Real.log (1 + Real.exp L / 2) ≤ L := by
    calc
      _ ≤ Real.log (Real.exp L) := Real.log_le_log (by positivity)
        (by linarith only [hs.2.2.2.2.1] : 1 + Real.exp L / 2 ≤ Real.exp L)
      _ = L := Real.log_exp L
  calc
    _ ≤ 6 * (380021600 * L ^ 2) * (2 * Real.exp (L ^ 9) * Real.exp (-(L ^ 8 / 20000000))) *
        Real.exp 1 * L := by
      gcongr
      exact Real.log_nonneg (by have hp := Real.exp_pos L; linarith only [hp])
    _ = _ := by ring

lemma lemma81_principal_mass_horizontal_budget {L x C : ℝ}
    (hL : 10000000 ≤ L) (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (L ^ 9))
    (hC : 0 ≤ C) :
    (4 * (360000000 * L ^ 2 + 20021600 * L) + 4 * C * (Real.exp (L / 3)) ^ 2) *
        x ^ 2 * Real.exp (1 / (Real.exp (L / 3)) ^ 2 -
          (Real.exp L / 2) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) / (Real.exp L / 2) ≤
      (12160691200 + 32 * C) * Real.exp (L ^ 9) * L ^ 3 * Real.exp (-(L ^ 8)) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hM := lemma81_principal_mass_moment_budget hL
  have hs := lemma56_principal_mass_scale_parameters hL
  have hD1 : 1 ≤ Real.exp L := Real.one_le_exp hL0
  have hMD := mul_le_mul_of_nonneg_left hD1 hM.1
  have hCB := mul_le_mul_of_nonneg_left hs.2.2.2.1 hC
  have hcoeff : 4 * (360000000 * L ^ 2 + 20021600 * L) + 4 * C * (Real.exp (L / 3)) ^ 2 ≤
      (4 * (360000000 * L ^ 2 + 20021600 * L) + 4 * C) * Real.exp L := by
    nlinarith only [hMD, hCB]
  have hxp : 0 ≤ x := by linarith only [hx]
  have hx2 := pow_le_pow_left₀ hxp hxmax 2
  have hgauss := lemma56_principal_mass_horizontal_gaussian_budget hL
  have heq : (Real.exp (L ^ 9)) ^ 2 * Real.exp (-3 * L ^ 9) =
      Real.exp (L ^ 9) * Real.exp (-2 * L ^ 9) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hL23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL3 : 1 ≤ L ^ 3 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL1 3
  have hCb := mul_le_mul_of_nonneg_left hL3 hC
  have hpoly : 32 * (360000000 * L ^ 2 + 20021600 * L) + 32 * C ≤
      (12160691200 + 32 * C) * L ^ 3 := by
    nlinarith only [hM.2, hL23, hCb]
  have hL89 : L ^ 8 ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
  have he : Real.exp (-2 * L ^ 9) ≤ Real.exp (-(L ^ 8)) :=
    Real.exp_le_exp.mpr (by linarith only [hL89, pow_nonneg hL0 9])
  calc
    _ ≤ ((4 * (360000000 * L ^ 2 + 20021600 * L) + 4 * C) * Real.exp L) *
        (2 * Real.exp (L ^ 9)) ^ 2 * Real.exp (-3 * L ^ 9) / (Real.exp L / 2) := by
      gcongr
    _ = (32 * (360000000 * L ^ 2 + 20021600 * L) + 32 * C) *
        ((Real.exp (L ^ 9)) ^ 2 * Real.exp (-3 * L ^ 9)) := by
      field_simp [(Real.exp_pos L).ne']; ring
    _ = (32 * (360000000 * L ^ 2 + 20021600 * L) + 32 * C) *
        Real.exp (L ^ 9) * Real.exp (-2 * L ^ 9) := by rw [heq]; ring
    _ ≤ ((12160691200 + 32 * C) * L ^ 3) * Real.exp (L ^ 9) * Real.exp (-(L ^ 8)) := by
      gcongr
    _ = _ := by ring

noncomputable def lemma81PrincipalMassErrorConstant : ℝ :=
  4560259200 * Real.exp 1 + 12160691200 + 32 * lemma56GaussianRightConstant

lemma lemma81_principal_mass_error_constant_pos : 0 < lemma81PrincipalMassErrorConstant := by
  have hC := lemma56_gaussian_right_constant_nonneg
  unfold lemma81PrincipalMassErrorConstant
  positivity

lemma lemma81_principal_mass_main_error_budget {L x : ℝ}
    (hL : 10000000 ≤ L) (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (L ^ 9)) :
    6 * (360000000 * L ^ 2 + 20021600 * L) * x ^ (1 - 1 / (20000000 * L)) *
      Real.exp ((1 - 1 / (20000000 * L)) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) *
        Real.log (1 + Real.exp L / 2) +
      (4 * (360000000 * L ^ 2 + 20021600 * L) + 4 * lemma56GaussianRightConstant * (Real.exp (L / 3)) ^ 2) *
        x ^ 2 * Real.exp (1 / (Real.exp (L / 3)) ^ 2 -
          (Real.exp L / 2) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) / (Real.exp L / 2) ≤
      lemma81PrincipalMassErrorConstant * Real.exp (L ^ 9) * L ^ 3 * Real.exp (-(L ^ 8 / 20000000)) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hl := lemma81_principal_mass_left_budget hL hx hxmax
  have hh := lemma81_principal_mass_horizontal_budget hL hx hxmax lemma56_gaussian_right_constant_nonneg
  have hex : Real.exp (-(L ^ 8)) ≤ Real.exp (-(L ^ 8 / 20000000)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [pow_nonneg hL0 8]
  have hC := lemma56_gaussian_right_constant_nonneg
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hex
    (by positivity : 0 ≤ (12160691200 + 32 * lemma56GaussianRightConstant) * Real.exp (L ^ 9) * L ^ 3))
  unfold lemma81PrincipalMassErrorConstant
  linarith only [hl, hh']

lemma lemma81_principal_mass_polynomial_absorption {L : ℝ} (hL : 10000000 ≤ L) :
    L ^ 3 * Real.exp (-(L ^ 8 / 20000000)) ≤ L ^ (-197 : ℤ) := by
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hL7 : L ≤ L ^ 7 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 7)
  have hscale := mul_le_mul_of_nonneg_right (by linarith only [hL, hL7] : (5000000 : ℝ) ≤ L ^ 7) hLp.le
  have hmargin : (200 : ℝ) * L / 800 ≤ L ^ 8 / 20000000 := by
    rw [show L ^ 7 * L = L ^ 8 by ring] at hscale
    linarith only [hscale]
  have he : L ^ 200 ≤ Real.exp (L ^ 8 / 20000000) :=
    (lemma56_principal_mass_exp_power hL 200).trans (Real.exp_le_exp.mpr (by simpa using hmargin))
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-(L ^ 8 / 20000000)))
  have hex : Real.exp (L ^ 8 / 20000000) * Real.exp (-(L ^ 8 / 20000000)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hex] at hm
  rw [zpow_neg, inv_eq_one_div]
  apply (le_div_iff₀ (pow_pos hLp 197)).mpr
  convert hm using 1; ring

end ZhangLS.Spec
