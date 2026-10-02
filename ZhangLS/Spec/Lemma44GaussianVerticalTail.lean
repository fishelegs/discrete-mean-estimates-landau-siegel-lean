import ZhangLS.Spec.Lemma44HorizontalGrowth
import ZhangLS.Spec.Lemma44ReflectedTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Gaussian truncation of a vertical Bochner integral

This separates the two actual infinite tails and bounds each by an
integrable exponential. The right product line is controlled by the fixed
absolutely convergent divisor series, uniformly in its imaginary part.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma44_gaussian_integral_truncation (f : ℝ → ℂ) (hf : Integrable f)
    {C b T : ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hT : 0 < T)
    (hbound : ∀ v, ‖f v‖ ≤ C * Real.exp (-b * v ^ 2)) :
    ‖(∫ v : ℝ, f v) - (∫ v : ℝ in -T..T, f v)‖ ≤
      2 * C * Real.exp (-b * T ^ 2) / (b * T) := by
  have hK : 0 < b * T := mul_pos hb hT
  have hright : ‖∫ v : ℝ in Ioi T, f v‖ ≤
      C * (Real.exp (-b * T ^ 2) / (b * T)) := by
    have hi := (integrableOn_exp_mul_Ioi (a := -(b * T)) (by linarith) T).const_mul C
    have hm : ∀ᵐ v ∂volume.restrict (Ioi T), ‖f v‖ ≤ C * Real.exp (-(b * T) * v) := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro v hv
      change T < v at hv
      apply (hbound v).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      have hquad : T * v ≤ v ^ 2 := by nlinarith only [hv, hT]
      nlinarith only [mul_le_mul_of_nonneg_left hquad hb.le]
    apply (norm_integral_le_of_norm_le hi hm).trans_eq
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(b * T) < 0)]
    rw [neg_div_neg_eq]
    congr 2
    ring
  have hleft : ‖∫ v : ℝ in Iic (-T), f v‖ ≤
      C * (Real.exp (-b * T ^ 2) / (b * T)) := by
    have hi := (integrableOn_exp_mul_Iic hK (-T)).const_mul C
    have hm : ∀ᵐ v ∂volume.restrict (Iic (-T)), ‖f v‖ ≤ C * Real.exp ((b * T) * v) := by
      refine ae_restrict_of_forall_mem measurableSet_Iic ?_
      intro v hv
      change v ≤ -T at hv
      apply (hbound v).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      have hquad : T * (-v) ≤ v ^ 2 := by nlinarith only [hv, hT]
      nlinarith only [mul_le_mul_of_nonneg_left hquad hb.le]
    apply (norm_integral_le_of_norm_le hi hm).trans_eq
    rw [integral_const_mul, integral_exp_mul_Iic hK]
    congr 1
    congr 1 <;> ring
  have hsplit : (∫ v : ℝ, f v) - (∫ v : ℝ in -T..T, f v) =
      (∫ v : ℝ in Iic (-T), f v) + (∫ v : ℝ in Ioi T, f v) := by
    have h1 := intervalIntegral.integral_Iic_add_Ioi
      (b := T) hf.integrableOn hf.integrableOn
    have h2 := intervalIntegral.integral_Iic_sub_Iic
      (a := -T) (b := T) hf.integrableOn hf.integrableOn
    linear_combination -h1 + h2
  rw [hsplit]
  exact (norm_add_le _ _).trans (by
    have h := add_le_add hleft hright
    convert h using 1 <;> ring)

theorem lemma44_product_series_norm_le_divisor_mass {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {z : ℂ} (hz : 5 / 4 ≤ z.re) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖DirichletCharacter.LFunction ψ z *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) z‖ ≤
      lemma44DivisorSeriesMass := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hs : 1 < z.re := by linarith
  rw [lemma44_product_LFunction_eq_LSeries χ ψ hs]
  let c := fun n => lemma23NuArithmeticFunction χ n * ψ (n : ZMod p)
  have hpoint (n : ℕ) : ‖LSeries.term c z n‖ ≤
      ‖LSeries.term lemma44DivisorCoefficient (5 / 4 : ℂ) n‖ := by
    by_cases hn : n = 0
    · simp [hn]
    · have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
      have hc : ‖c n‖ ≤ ‖lemma44DivisorCoefficient n‖ := by
        rw [lemma44_divisor_coefficient_norm]
        dsimp [c]
        rw [norm_mul]
        simpa using mul_le_mul (lemma23NuArithmeticFunction_norm_le_card_divisors χ n)
          (ψ.norm_le_one _) (norm_nonneg _) (by positivity)
      rw [lemma44_norm_LSeries_term_eq_real_exp _ _ hn,
        lemma44_norm_LSeries_term_eq_real_exp _ _ hn]
      rw [show (5 / 4 : ℂ).re = (5 / 4 : ℝ) by norm_num]
      apply mul_le_mul hc _ (Real.exp_nonneg _) (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right hz hlog]
  have hsum := summable_norm_iff.mpr (lemma44_product_series_summable χ ψ hs)
  have hdiv := summable_norm_iff.mpr lemma44_divisor_series_summable
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hpoint hdiv)

theorem lemma44_right_mellin_gaussian_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma44InOmega3 D s) (v : ℝ) :
    ‖lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I‖ ≤
      (lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * lemma23PaperL D ^ 9)) *
        Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let w : ℂ := 1 + (v : ℂ) * I
  have hL0 : 0 < lemma23PaperL D := by linarith
  have ha : lemma44PaperAlpha D ≤ 1 / 4 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    apply (div_le_iff₀ (pow_pos hL0 9)).mpr
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 3
    have h39 := pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (show 3 ≤ 9 by norm_num)
    norm_num at h3
    nlinarith only [h3, h39, Real.pi_le_four]
  have hz : 5 / 4 ≤ (s + w).re := by simp [w]; linarith only [hs.1, ha]
  have hp := lemma44_product_series_norm_le_divisor_mass χ ψ hz
  rw [norm_mul] at hp
  have hmass := lemma44_divisor_series_mass_nonneg
  have hn : 1 ≤ ‖w‖ := by simpa [w] using Complex.abs_re_le_norm w
  have hinv : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hscale : ‖exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ =
      Real.exp ((9 / 5 : ℝ) * lemma23PaperL D ^ 9) := by
    rw [norm_exp, mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero,
      lemma44_paper_gaussian_scale_log]
    simp [w]
  have homega : ‖lemma57OmegaOne D w‖ ≤
      Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
    change ‖lemma57OmegaOne D (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ _
    rw [lemma44_Omega_norm_vertical, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hL0 : 0 < lemma23PaperL D := by linarith
    have hp30 : 1 ≤ lemma23PaperL D ^ 30 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
    field_simp
    nlinarith only [hp30]
  unfold lemma44ProductMellinIntegrand
  change ‖(DirichletCharacter.LFunction ψ (s + w) *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (s + w)) *
    exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ)) * lemma57OmegaOne D w / w * I‖ ≤ _
  simp only [norm_mul, norm_inv, norm_I, mul_one, div_eq_mul_inv]
  rw [hscale]
  calc
    _ ≤ lemma44DivisorSeriesMass * Real.exp ((9 / 5 : ℝ) * lemma23PaperL D ^ 9) *
        (Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2)) * 1 := by
      exact mul_le_mul (mul_le_mul
        (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)) homega
        (norm_nonneg _) (by positivity)) hinv (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

end ZhangLS.Spec
