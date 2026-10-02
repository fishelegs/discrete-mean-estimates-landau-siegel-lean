import ZhangLS.Spec.Lemma112HorizontalBounds
import ZhangLS.Spec.Lemma112ShortCutoff
/-! # Original-left Z error controlled by the original E₂, without extra floors -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_error_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s w : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 0) (hwi : |w.im| = lemma23PaperL D ^ 20)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    ‖lemma112ActualZErrorIntegrand χ ψ s z w‖ ≤
      4 * Real.exp 2 * Real.exp (2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ h1
  have hF := lemma112_error_horizontal_factor_bound χ ψ hψ hD hL hs hwr hwi hz
  have hN := lemma112_short_polynomial_norm_bound χ ψ⁻¹ (by linarith : 3 ≤ lemma23PaperL D)
    (s := 1 - s - w) (by simp only [sub_re, one_re, hs.1]; linarith only [hwr.2])
  have hwide : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 :=
    ⟨by linarith only [hwr.1,h9], by linarith only [hwr.2]⟩
  have hG := lemma61_large_shift_gaussian_bound (by linarith : 3 ≤ lemma23PaperL D) hwide
  have hgauss : w.im ^ 2 / (4 * lemma23PaperL D ^ 30) = lemma23PaperL D ^ 10 / 4 := by
    rw [← sq_abs w.im,hwi]
    field_simp
  rw [neg_div, hgauss] at hG
  calc
    _ = ‖(lemma112ErrorDifferenceNumerator χ ψ s w / w) *
        exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ *
      ‖lemma112ShortPolynomial χ ψ⁻¹ (1 - s - w)‖ * ‖lemma57OmegaOne D w‖ := by
        unfold lemma112ActualZErrorIntegrand
        simp only [norm_mul]
        ring
    _ ≤ (2 * Real.exp 1 * Real.exp (lemma23PaperL D ^ 9)) *
        (2 * Real.exp (lemma23PaperL D ^ 9)) *
        (Real.exp 1 * Real.exp (-(lemma23PaperL D ^ 10 / 4))) := by gcongr
    _ = _ := by
      rw [show 2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
          lemma23PaperL D ^ 9 + lemma23PaperL D ^ 9 + -(lemma23PaperL D ^ 10 / 4) by ring,
        show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      simp only [Real.exp_add]
      ring

lemma lemma112_error_horizontal_integral_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ))
    {t : ℝ} (ht : |t| = lemma23PaperL D ^ 20) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ x : ℝ in (-1 : ℝ)..0,
      lemma112ActualZErrorIntegrand χ ψ s z ((x : ℂ) + (t : ℂ) * I))‖ ≤
      4 * Real.exp 2 * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have hp : ∀ x ∈ uIoc (-1 : ℝ) 0,
      ‖lemma112ActualZErrorIntegrand χ ψ s z ((x : ℂ) + (t : ℂ) * I)‖ ≤
        4 * Real.exp 2 * Real.exp (2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) := by
    intro x hx
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    exact lemma112_error_horizontal_point_bound χ ψ hψ hD hL hs
      (by simpa using And.intro hx.1.le hx.2) (by simpa using ht) hz
  have hb := lemma112_normalized_integral_norm_le hp
  norm_num only [zero_sub, neg_neg, abs_one, mul_one] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h9 : 64 * lemma23PaperL D ^ 9 ≤ lemma23PaperL D ^ 10 := by
    convert mul_le_mul_of_nonneg_right hL (pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 9) using 1 <;> ring
  linarith only [h9, pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 9]

lemma lemma112_actual_original_left_Z_error_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    (hthreshold : lemma23SectionFourModulusThreshold ≤ D) (hs : Lemma112InRegion D s)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma112ActualZErrorIntegrand χ ψ s z ((-1 : ℂ) + (v : ℂ) * I) * I)‖ ≤
      (lemma51ErrorConstant + 8 * Real.exp 2) * lemma112ActualE2 χ ψ s := by
  let H := lemma23PaperL D ^ 20
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let F := lemma112ActualZErrorIntegrand χ ψ s z
  have h0 : 0 < H := by dsimp [H]; positivity
  have hshift := lemma112_actual_error_line_shift χ ψ hD (by linarith) hs z
  have hV := lemma112_actual_error_vertical_integral_bound χ ψ hthreshold hψ hs z
  have hV' : ‖c * (∫ v in -H..H, F (I * (v : ℂ)) * I)‖ ≤
      lemma51ErrorConstant * lemma112ActualE2 χ ψ s := by
    rw [intervalIntegral.integral_mul_const, norm_mul, norm_mul, norm_I, mul_one]
    exact (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one (norm_nonneg _)).trans
      (by simpa only [one_mul] using hV)
  have he := lemma112_exp_remainder_le_E2 χ ψ hL (by rw [hs.1]; norm_num)
  have hhb := lemma112_error_horizontal_integral_bound χ ψ hψ hD hL hs hz
    (t := -H) (by rw [abs_neg,abs_of_pos h0])
  have hht := lemma112_error_horizontal_integral_bound χ ψ hψ hD hL hs hz
    (t := H) (abs_of_pos h0)
  have hB : ‖c * (∫ x in (-1 : ℝ)..0, F ((x : ℂ) - (H : ℂ) * I))‖ ≤
      4 * Real.exp 2 * lemma112ActualE2 χ ψ s := by
    have hb := hhb.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 * Real.exp 2))
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hb
  have hT : ‖c * (∫ x in (-1 : ℝ)..0, F ((x : ℂ) + (H : ℂ) * I))‖ ≤
      4 * Real.exp 2 * lemma112ActualE2 χ ψ s :=
    hht.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 * Real.exp 2))
  rw [hshift, mul_sub, mul_add]
  have htri := norm_sub_le
    (c * (∫ v in -H..H, F (I * (v : ℂ)) * I) + c * (∫ x in (-1 : ℝ)..0, F ((x : ℂ) - (H : ℂ) * I)))
    (c * (∫ x in (-1 : ℝ)..0, F ((x : ℂ) + (H : ℂ) * I)))
  have hadd := norm_add_le
    (c * (∫ v in -H..H, F (I * (v : ℂ)) * I))
    (c * (∫ x in (-1 : ℝ)..0, F ((x : ℂ) - (H : ℂ) * I)))
  change ‖_ + _ - _‖ ≤ _
  nlinarith only [hV',hB,hT,htri,hadd]

end ZhangLS.Spec
