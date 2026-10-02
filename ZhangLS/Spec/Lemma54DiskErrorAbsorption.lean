import ZhangLS.Spec.Lemma54FullDiskBudget

/-! # One modulus threshold absorbs every polynomial-exponential disk error -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma54DiskConstant : ℝ := 10403 + lemma54DiskTailConstant

theorem lemma54_disk_constant_pos : 0 < lemma54DiskConstant := by
  unfold lemma54DiskConstant
  have h := lemma54_disk_tail_constant_pos
  positivity

theorem lemma54_disk_exponential_absorption_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      1 < D ∧ 2000 ≤ lemma23PaperL D ∧
        lemma23PaperL D ^ 3200 * Real.exp (-(lemma23PaperL D ^ 10) / 2) ≤
          lemma44PaperAlpha D * Real.log (lemma23PaperL D) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hf : Tendsto (fun D : ℕ => lemma23PaperL D ^ 3209 *
      Real.exp (-(1 / 2 : ℝ) * lemma23PaperL D)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat, Function.comp_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3209 : ℝ) (1 / 2) (by norm_num)).comp ht
  have hevent : ∀ᶠ D : ℕ in atTop,
      1 < D ∧ 2000 ≤ lemma23PaperL D ∧
        lemma23PaperL D ^ 3200 * Real.exp (-(lemma23PaperL D ^ 10) / 2) ≤
          lemma44PaperAlpha D * Real.log (lemma23PaperL D) := by
    filter_upwards [hf.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
      ht.eventually (eventually_ge_atTop 2000), eventually_ge_atTop (2 : ℕ)] with D hpoly hL hD
    refine ⟨by omega, hL, ?_⟩
    let L := lemma23PaperL D
    have hL1 : 1 ≤ L := by dsimp [L]; linarith
    have hLpos : 0 < L := by dsimp [L]; linarith
    have hpow : L ≤ L ^ 10 := by
      simpa only [pow_one] using pow_le_pow_right₀ hL1 (show (1 : ℕ) ≤ 10 by norm_num)
    have he : Real.exp (-(L ^ 10) / 2) ≤ Real.exp (-(1 / 2 : ℝ) * L) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hsmall : (L ^ 3200 * Real.exp (-(L ^ 10) / 2)) * L ^ 9 ≤ 1 := by
      calc
        _ = L ^ 3209 * Real.exp (-(L ^ 10) / 2) := by ring
        _ ≤ L ^ 3209 * Real.exp (-(1 / 2 : ℝ) * L) :=
          mul_le_mul_of_nonneg_left he (pow_nonneg hLpos.le _)
        _ ≤ 1 := hpoly.le
    have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLpos).2
      (Real.exp_one_lt_three.le.trans (by dsimp [L]; linarith : (3 : ℝ) ≤ L))
    have hplog : 1 ≤ Real.pi * Real.log L := by
      have hp := mul_le_mul_of_nonneg_right Real.two_le_pi (by linarith : 0 ≤ Real.log L)
      nlinarith
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp, div_mul_eq_mul_div]
    change L ^ 3200 * Real.exp (-(L ^ 10) / 2) ≤ (Real.pi * Real.log L) / L ^ 9
    exact (le_div_iff₀ (pow_pos hLpos 9)).2 (hsmall.trans hplog)
  exact eventually_atTop.mp hevent

theorem lemma54_actual_mellin_disk_uniform_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      1 < D ∧ 2000 ≤ lemma23PaperL D ∧
        ∀ s : ℂ, ‖s - 1‖ < 10 * lemma44PaperAlpha D →
          ‖lemma54PaperDeltaMellin D s - 1‖ ≤
            lemma54DiskConstant * lemma44PaperAlpha D * Real.log (lemma23PaperL D) := by
  obtain ⟨D₀, hD₀⟩ := lemma54_disk_exponential_absorption_threshold
  refine ⟨D₀, ?_⟩
  intro D hD
  have ht := hD₀ D hD
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro s hs
  have hb := lemma54_actual_mellin_disk_budget ht.1 ht.2.1 hs
  have he := mul_le_mul_of_nonneg_left ht.2.2 lemma54_disk_tail_constant_pos.le
  unfold lemma54DiskConstant
  nlinarith only [hb, he]

end ZhangLS.Spec
