import ZhangLS.Spec.Lemma44GaussianVerticalTail

/-! # The actual right vertical truncation error in Lemma 4.4 -/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma44_mellin_normalization_norm_le_one :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_mul, norm_mul, norm_I, mul_one]
  norm_num [Complex.norm_of_nonneg Real.pi_pos.le]
  have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.one_le_pi_div_two]
  have h := inv_le_one_of_one_le₀ hpi
  rw [abs_of_pos Real.pi_pos]
  convert h using 1
  ring

theorem lemma44_modulus_one_lt_at_threshold {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : lemma23SectionFourModulusThreshold ≤ D) : 1 < D := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hDp : (0 : ℝ) < D := by exact_mod_cast χ.modulus_pos
  have hDr : (1 : ℝ) < D := by
    have h := Real.exp_lt_exp.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hL)
    simpa [lemma23PaperL, Real.exp_log hDp] using h
  exact_mod_cast hDr

theorem lemma44_right_vertical_truncation_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I) -
        lemma44TruncatedProductMellin χ ψ s (lemma44PaperGaussianScale D) 1
          (lemma23PaperL D ^ 20)‖ ≤
      8 * lemma44DivisorSeriesMass * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  let L := lemma23PaperL D
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hmass := lemma44_divisor_series_mass_nonneg
  have hB : 0 < lemma44PaperGaussianScale D := by
    unfold lemma44PaperGaussianScale lemma23PaperP
    exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hi := (lemma44_product_gaussian_mellin_identity χ ψ s
    (lemma44_modulus_one_lt_at_threshold χ hD) hB (by norm_num : (0 : ℝ) < 1)
    (by linarith only [lemma44_omega3_re_pos hL hs])).1.mul_const I
  have hg := lemma44_gaussian_integral_truncation _ hi
    (mul_nonneg lemma44_divisor_series_mass_nonneg (Real.exp_nonneg _))
    (by positivity : 0 < 1 / (4 * L ^ 30)) (pow_pos hL0 20)
    (lemma44_right_mellin_gaussian_bound χ ψ hL hs)
  have he : 1 / (4 * L ^ 30) * (L ^ 20) ^ 2 = L ^ 10 / 4 := by
    field_simp
  have hk : 1 / (4 * L ^ 30) * L ^ 20 = (4 * L ^ 10)⁻¹ := by
    field_simp
  change ‖_ - _‖ ≤ _ at hg
  rw [neg_mul, he, hk, div_eq_mul_inv, inv_inv] at hg
  have hb : L ^ 10 * Real.exp ((9 / 5 : ℝ) * L ^ 9 - L ^ 10 / 4) ≤ L ^ (-180 : ℤ) := by
    calc
      _ ≤ L ^ 2000 * Real.exp (30 * L ^ 9 + 100 * L - L ^ 10 / 4) := by
        apply mul_le_mul
          (pow_le_pow_right₀ hL1 (show 10 ≤ 2000 by norm_num))
          (Real.exp_le_exp.mpr (by nlinarith only [hL0, pow_nonneg hL0.le 9]))
          (Real.exp_nonneg _) (pow_nonneg hL0.le 2000)
      _ ≤ _ := lemma44_horizontal_decay_budget (lemma44_log_large_at_threshold hD)
  have heprod : Real.exp (1 + (9 / 5 : ℝ) * L ^ 9) * Real.exp (-(L ^ 10 / 4)) =
      Real.exp 1 * Real.exp ((9 / 5 : ℝ) * L ^ 9 - L ^ 10 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hg' : ‖(∫ v : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I) -
      (∫ v : ℝ in -(L ^ 20)..L ^ 20,
        lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I)‖ ≤
      8 * lemma44DivisorSeriesMass * Real.exp 1 * L ^ (-180 : ℤ) := by
    apply hg.trans
    calc
      _ = (8 * lemma44DivisorSeriesMass * Real.exp 1) *
          (L ^ 10 * Real.exp ((9 / 5 : ℝ) * L ^ 9 - L ^ 10 / 4)) := by
        dsimp only [L]
        rw [show 2 * (lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * lemma23PaperL D ^ 9)) *
            Real.exp (-(lemma23PaperL D ^ 10 / 4)) * (4 * lemma23PaperL D ^ 10) =
          8 * lemma44DivisorSeriesMass * lemma23PaperL D ^ 10 *
            (Real.exp (1 + (9 / 5 : ℝ) * lemma23PaperL D ^ 9) * Real.exp (-(lemma23PaperL D ^ 10 / 4)))
          by ring]
        rw [heprod]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  unfold lemma44TruncatedProductMellin
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right lemma44_mellin_normalization_norm_le_one (norm_nonneg _)).trans
    (by simpa only [one_mul] using hg')

end ZhangLS.Spec
