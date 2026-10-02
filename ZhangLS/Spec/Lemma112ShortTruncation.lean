import ZhangLS.Spec.Lemma112HorizontalBounds
import ZhangLS.Spec.Lemma112ShortCutoff
/-! # Finite dual Gaussian Mellin truncation at the actual complementary scale -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_short_right_gaussian_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {B : ℝ} (hlogB : Real.log B ≤ lemma23PaperL D ^ 9)
    {s : ℂ} (hs : 0 ≤ s.re) (v : ℝ) :
    ‖lemma112ShortRightMellinIntegrand χ ψ s B 1 v * I‖ ≤
      (2 * Real.exp (1 + 5 * lemma23PaperL D ^ 9)) *
        Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
  let w : ℂ := 1 + (v : ℂ) * I
  have h0 : 0 < lemma23PaperL D := by linarith
  have hwp : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 := by
    simp only [w, add_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    constructor <;> nlinarith only [pow_nonneg h0.le 9]
  have hp := lemma112_short_polynomial_norm_bound χ ψ hL (s := s + w) (by simp [w]; linarith only [hs])
  have hn : 1 ≤ ‖w‖ := by simpa [w] using Complex.abs_re_le_norm w
  have hinv : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hscale : ‖exp (w * (Real.log B : ℂ))‖ ≤ Real.exp (lemma23PaperL D ^ 9) := by
    rw [norm_exp]
    simpa [w] using Real.exp_le_exp.mpr hlogB
  have homega : ‖lemma57OmegaOne D w‖ ≤
      Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
    have h := lemma61_large_shift_gaussian_bound hL hwp
    convert h using 1 <;> simp [w] <;> congr 1 <;> ring
  unfold lemma112ShortRightMellinIntegrand
  change ‖lemma112ShortPolynomial χ ψ (s + w) * exp (w * (Real.log B : ℂ)) *
    lemma57OmegaOne D w / w * I‖ ≤ _
  simp only [norm_mul, norm_inv, norm_I, mul_one, div_eq_mul_inv]
  calc
    _ ≤ (2 * Real.exp (lemma23PaperL D ^ 9)) * Real.exp (lemma23PaperL D ^ 9) *
        (Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2)) * 1 := by
      gcongr <;> simp [one_div]
    _ = 2 * Real.exp (1 + 2 * lemma23PaperL D ^ 9) *
        Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
      rw [show 1 + 2 * lemma23PaperL D ^ 9 = lemma23PaperL D ^ 9 + lemma23PaperL D ^ 9 + 1 by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (by nlinarith only [pow_nonneg h0.le 9])) (by norm_num)) (Real.exp_nonneg _)

lemma lemma112_actual_short_right_truncation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (hD : 1 < D)
    (hL : 64 ≤ lemma23PaperL D) {B : ℝ} (hlogB : Real.log B ≤ lemma23PaperL D ^ 9) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(∫ v : ℝ, lemma112ShortRightMellinIntegrand χ ψ s B 1 v * I) -
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma112ShortRightMellinIntegrand χ ψ s B 1 v * I)‖ ≤
      16 * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hi := (lemma112_short_mellin_integrable χ ψ s B hD
    (by norm_num : (1 : ℝ) ≠ 0)).mul_const I
  have ht := lemma44_gaussian_integral_truncation
    (fun v => lemma112ShortRightMellinIntegrand χ ψ s B 1 v * I) hi
    (C := 2 * Real.exp (1 + 5 * lemma23PaperL D ^ 9))
    (b := 1 / (4 * lemma23PaperL D ^ 30)) (T := lemma23PaperL D ^ 20)
    (by positivity) (by positivity) (by positivity)
    (lemma112_short_right_gaussian_bound χ ψ (by linarith) hlogB hs)
  have hbt : (1 / (4 * lemma23PaperL D ^ 30)) * lemma23PaperL D ^ 20 =
      1 / (4 * lemma23PaperL D ^ 10) := by field_simp
  have hbe : (1 / (4 * lemma23PaperL D ^ 30)) * (lemma23PaperL D ^ 20) ^ 2 =
      lemma23PaperL D ^ 10 / 4 := by field_simp
  apply ht.trans
  calc
    _ = 16 * (lemma23PaperL D ^ 10 * Real.exp
        (1 + 5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      rw [hbt,show -(1 / (4 * lemma23PaperL D ^ 30)) *
        (lemma23PaperL D ^ 20) ^ 2 = -(lemma23PaperL D ^ 10 / 4) by linarith only [hbe]]
      rw [show 1 + 5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
        (1 + 5 * lemma23PaperL D ^ 9) + -(lemma23PaperL D ^ 10 / 4) by ring]
      simp only [Real.exp_add]
      field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma61_short_gaussian_exponent_absorption hL)
      (by norm_num)

lemma lemma112_actual_finite_short_mellin_dual_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : s.re ≤ 1)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma112ShortRightMellinIntegrand χ ψ (1 - s) (lemma112DualScale D z) 1 t * I) -
      lemma112GaussianSeries χ ψ (lemma112DualScale D z) (1 - s)‖ ≤
      (16 + lemma44InverseSquareMass) * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  let F := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ t : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma112ShortRightMellinIntegrand χ ψ (1 - s) (lemma112DualScale D z) 1 t * I)
  let J := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ t : ℝ, lemma112ShortRightMellinIntegrand χ ψ (1 - s) (lemma112DualScale D z) 1 t * I)
  have hr : 0 ≤ (1 - s).re := by simpa using sub_nonneg.mpr hs
  have hlog := lemma112_dual_scale_log_bounds hD hL hz
  have ht := lemma112_actual_short_right_truncation χ ψ hD hL hlog.2 hr
  have hn : ‖F - J‖ ≤ 16 * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    dsimp [F,J]
    rw [← mul_sub, norm_mul]
    exact (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one (norm_nonneg _)).trans
      (by simpa only [one_mul, norm_sub_rev] using ht)
  have hi : J = lemma112FiniteGaussianSum χ ψ (lemma112DualScale D z) (1 - s) :=
    lemma112_actual_short_gaussian_mellin χ ψ (1 - s) hD (lemma112_dual_scale_pos hD z) (by norm_num)
  have hc := lemma112_finite_gaussian_cutoff_bound χ ψ hD (by linarith)
    (lemma112_dual_scale_pos hD z) (hlog.2.trans (by nlinarith only [hlog.1,hlog.2]))
    (lemma112_dual_scale_twice_below_cutoff hD hL hz.1) hr
  have he : Real.exp (-(lemma23PaperL D ^ 10)) ≤ Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ lemma23PaperL D ^ 10 := by positivity
    linarith only [h0]
  have hm : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hc' : ‖J - lemma112GaussianSeries χ ψ (lemma112DualScale D z) (1 - s)‖ ≤
      lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    rw [hi, norm_sub_rev]
    exact hc.trans (mul_le_mul_of_nonneg_left he hm)
  have htri := norm_sub_le_norm_sub_add_norm_sub F J (lemma112GaussianSeries χ ψ (lemma112DualScale D z) (1 - s))
  change ‖F - _‖ ≤ _
  nlinarith only [hn, hc', htri]

end ZhangLS.Spec
