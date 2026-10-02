import ZhangLS.Spec.Lemma56PrincipalMassScales

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_principal_mass_left_budget {L x : ℝ} (hL : 10000000 ≤ L)
    (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (L ^ 9)) :
    6 * (18 * L ^ 2 + 21601 * L) * x ^ (1 - 1 / L) *
      Real.exp ((1 - 1 / L) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) *
        Real.log (1 + Real.exp L / 2) ≤
      259428 * Real.exp 1 * Real.exp (L ^ 9) * L ^ 3 * Real.exp (-(L ^ 8)) := by
  have hLp : 0 < L := by linarith only [hL]
  have hL0 : 0 ≤ L := hLp.le
  have hs := lemma56_principal_mass_scale_parameters hL
  have ha0 : 0 ≤ 1 - 1 / L := by linarith only [hs.1]
  have hM := (lemma56_principal_mass_moment_budget hL).2
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hP : 0 < Real.exp (L ^ 9) := Real.exp_pos _
  have hpow : x ^ (1 - 1 / L) ≤
      2 * Real.exp (L ^ 9) * Real.exp (-(L ^ 8)) := by
    have htwo : (2 : ℝ) ^ (1 - 1 / L) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs.2.1
    calc
      _ ≤ (2 * Real.exp (L ^ 9)) ^ (1 - 1 / L) := Real.rpow_le_rpow hx0 hxmax ha0
      _ = (2 : ℝ) ^ (1 - 1 / L) * (Real.exp (L ^ 9)) ^ (1 - 1 / L) :=
        Real.mul_rpow (by norm_num) hP.le
      _ ≤ 2 * (Real.exp (L ^ 9)) ^ (1 - 1 / L) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hP.le _)
      _ = _ := by
        rw [lemma56_principal_mass_left_power hLp]
        rw [show Real.exp (L ^ 9 - L ^ 8) = Real.exp (L ^ 9) * Real.exp (-(L ^ 8)) by
          rw [← Real.exp_add]; congr 1]
        ring
  have ha2 : (1 - 1 / L) ^ 2 ≤ 1 := by nlinarith only [hs.1, hs.2.1]
  have hB2 : 1 ≤ (Real.exp (L / 3)) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs.2.2.1 2
    simpa only [one_pow] using hh
  have hex : Real.exp ((1 - 1 / L) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_one (by positivity : 0 < 4 * (Real.exp (L / 3)) ^ 2)).mpr
    linarith only [ha2, hB2]
  have hlog : Real.log (1 + Real.exp L / 2) ≤ L := by
    calc
      _ ≤ Real.log (Real.exp L) := Real.log_le_log (by positivity)
        (by linarith only [hs.2.2.2.2.1] : 1 + Real.exp L / 2 ≤ Real.exp L)
      _ = L := Real.log_exp L
  calc
    _ ≤ 6 * (21619 * L ^ 2) * (2 * Real.exp (L ^ 9) * Real.exp (-(L ^ 8))) *
        Real.exp 1 * L := by
      gcongr
      exact Real.log_nonneg (by have hp := Real.exp_pos L; linarith only [hp])
    _ = _ := by ring

lemma lemma56_principal_mass_height_exponent {L : ℝ} (hL : 10000000 ≤ L) :
    4 * L ^ 9 ≤ Real.exp (4 * L / 3) / 16 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL2 : 2 ≤ L := by linarith only [hL]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL2 7
  norm_num at hp
  have hm := mul_le_mul_of_nonneg_right (by linarith only [hp] : 64 ≤ L ^ 7) (pow_nonneg hL0 9)
  rw [show L ^ 7 * L ^ 9 = L ^ 16 by ring] at hm
  have he := (lemma56_principal_mass_exp_power hL 16).trans
    (Real.exp_le_exp.mpr (by norm_num; linarith only [hL0] : (16 : ℝ) * L / 800 ≤ 4 * L / 3))
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  linarith only [he, hm]

lemma lemma56_principal_mass_horizontal_exponent_identity (L : ℝ) :
    1 / (Real.exp (L / 3)) ^ 2 - (Real.exp L / 2) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2) =
      Real.exp (-2 * L / 3) - Real.exp (4 * L / 3) / 16 := by
  have hB : (Real.exp (L / 3)) ^ 2 = Real.exp (2 * L / 3) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hD : (Real.exp L) ^ 2 = Real.exp (2 * L) := by rw [← Real.exp_nat_mul]; norm_num
  have hrec : 1 / Real.exp (2 * L / 3) = Real.exp (-2 * L / 3) := by
    calc
      _ = (Real.exp (2 * L / 3))⁻¹ := one_div _
      _ = Real.exp (-(2 * L / 3)) := (Real.exp_neg _).symm
      _ = _ := by congr 1; ring
  have hquot : Real.exp (2 * L) / Real.exp (2 * L / 3) = Real.exp (4 * L / 3) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [div_pow, hD]
  simp_rw [hB]
  calc
    _ = 1 / Real.exp (2 * L / 3) - (Real.exp (2 * L) / Real.exp (2 * L / 3)) / 16 := by ring
    _ = _ := by rw [hrec, hquot]

lemma lemma56_principal_mass_horizontal_gaussian_budget {L : ℝ} (hL : 10000000 ≤ L) :
    Real.exp (1 / (Real.exp (L / 3)) ^ 2 -
      (Real.exp L / 2) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) ≤ Real.exp (-3 * L ^ 9) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hL9 : 1 ≤ L ^ 9 := by simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL1 9
  have he : Real.exp (-2 * L / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hL0])
  have hh := lemma56_principal_mass_height_exponent hL
  apply Real.exp_le_exp.mpr
  rw [lemma56_principal_mass_horizontal_exponent_identity]
  linarith only [he, hh, hL9]

lemma lemma56_principal_mass_horizontal_budget {L x C : ℝ}
    (hL : 10000000 ≤ L) (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (L ^ 9))
    (hC : 0 ≤ C) :
    (4 * (18 * L ^ 2 + 21601 * L) + 4 * C * (Real.exp (L / 3)) ^ 2) *
        x ^ 2 * Real.exp (1 / (Real.exp (L / 3)) ^ 2 -
          (Real.exp L / 2) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) / (Real.exp L / 2) ≤
      (691808 + 32 * C) * Real.exp (L ^ 9) * L ^ 3 * Real.exp (-(L ^ 8)) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hM := lemma56_principal_mass_moment_budget hL
  have hs := lemma56_principal_mass_scale_parameters hL
  have hD1 : 1 ≤ Real.exp L := Real.one_le_exp hL0
  have hMD := mul_le_mul_of_nonneg_left hD1 hM.1
  have hCB := mul_le_mul_of_nonneg_left hs.2.2.2.1 hC
  have hcoeff : 4 * (18 * L ^ 2 + 21601 * L) + 4 * C * (Real.exp (L / 3)) ^ 2 ≤
      (4 * (18 * L ^ 2 + 21601 * L) + 4 * C) * Real.exp L := by
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
  have hpoly : 32 * (18 * L ^ 2 + 21601 * L) + 32 * C ≤
      (691808 + 32 * C) * L ^ 3 := by
    nlinarith only [hM.2, hL23, hCb]
  have hL89 : L ^ 8 ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
  have he : Real.exp (-2 * L ^ 9) ≤ Real.exp (-(L ^ 8)) :=
    Real.exp_le_exp.mpr (by linarith only [hL89, pow_nonneg hL0 9])
  calc
    _ ≤ ((4 * (18 * L ^ 2 + 21601 * L) + 4 * C) * Real.exp L) *
        (2 * Real.exp (L ^ 9)) ^ 2 * Real.exp (-3 * L ^ 9) / (Real.exp L / 2) := by
      gcongr
    _ = (32 * (18 * L ^ 2 + 21601 * L) + 32 * C) *
        ((Real.exp (L ^ 9)) ^ 2 * Real.exp (-3 * L ^ 9)) := by
      field_simp [(Real.exp_pos L).ne'] <;> ring
    _ = (32 * (18 * L ^ 2 + 21601 * L) + 32 * C) *
        Real.exp (L ^ 9) * Real.exp (-2 * L ^ 9) := by rw [heq]; ring
    _ ≤ ((691808 + 32 * C) * L ^ 3) * Real.exp (L ^ 9) * Real.exp (-(L ^ 8)) := by
      gcongr
    _ = _ := by ring

end ZhangLS.Spec
