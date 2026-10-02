import ZhangLS.Spec.Lemma56PrincipalPerronMainError

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_principal_mass_exp_base {L : ℝ} (hL : 10000000 ≤ L) :
    L ≤ Real.exp (L / 800) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hbig : 2560000 ≤ L := by linarith only [hL]
  have hm := mul_le_mul_of_nonneg_right hbig hL0
  have hpoly : L ≤ (1 + L / 1600) ^ 2 := by nlinarith only [hm, hL0]
  have he : 1 + L / 1600 ≤ Real.exp (L / 1600) := by
    simpa only [add_comm] using Real.add_one_le_exp (L / 1600)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + L / 1600) he 2
  have hex : (Real.exp (L / 1600)) ^ 2 = Real.exp (L / 800) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hex] at hp
  exact hpoly.trans hp

lemma lemma56_principal_mass_exp_power {L : ℝ} (hL : 10000000 ≤ L) (n : ℕ) :
    L ^ n ≤ Real.exp ((n : ℝ) * L / 800) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hp := pow_le_pow_left₀ hL0 (lemma56_principal_mass_exp_base hL) n
  rw [← Real.exp_nat_mul] at hp
  exact hp.trans_eq (by congr 1; ring)

lemma lemma56_principal_mass_left_power {L : ℝ} (hL : 0 < L) :
    (Real.exp (L ^ 9)) ^ (1 - 1 / L) = Real.exp (L ^ 9 - L ^ 8) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp [hL.ne'] <;> ring

lemma lemma56_principal_mass_moment_budget {L : ℝ} (hL : 10000000 ≤ L) :
    0 ≤ 18 * L ^ 2 + 21601 * L ∧
      18 * L ^ 2 + 21601 * L ≤ 21619 * L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hm := mul_le_mul_of_nonneg_right hL1 hL0
  exact ⟨by positivity, by nlinarith only [hm]⟩

lemma lemma56_principal_mass_scale_parameters {L : ℝ} (hL : 10000000 ≤ L) :
    (1 / 2 : ℝ) ≤ 1 - 1 / L ∧ 1 - 1 / L ≤ 1 ∧
      1 ≤ Real.exp (L / 3) ∧ (Real.exp (L / 3)) ^ 2 ≤ Real.exp L ∧
      1 ≤ Real.exp L / 2 ∧ Real.exp L / 2 ≤ Real.exp L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hLp : 0 < L := by linarith only [hL]
  have hinv : 1 / L ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ hLp (by norm_num)).mpr
    linarith only [hL]
  have hB : 1 ≤ Real.exp (L / 3) := Real.one_le_exp (by positivity)
  have hB2 : (Real.exp (L / 3)) ^ 2 ≤ Real.exp L := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith only [hL0]
  have he := Real.add_one_le_exp L
  have hpInv : 0 ≤ 1 / L := by positivity
  exact ⟨by linarith only [hinv], by linarith only [hpInv], hB, hB2,
    by linarith only [he, hL], by have hp := Real.exp_pos L; linarith only [hp]⟩

end ZhangLS.Spec
