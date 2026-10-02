import ZhangLS.Spec.Lemma112ReciprocalContour
/-! # Uniform Gaussian budgets for all reciprocal-tail edges -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_normalized_integral_norm_le {f : ℝ → ℂ} {a b C : ℝ}
    (h : ∀ x ∈ uIoc a b, ‖f x‖ ≤ C) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ x in a..b, f x)‖ ≤ C * |b - a| := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one (norm_nonneg _)).trans
    (by simpa only [one_mul] using intervalIntegral.norm_integral_le_of_norm_le_const h)

lemma lemma112_reciprocal_far_left_integral_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    {z : ℝ} (hz : 1 / 2 ≤ z) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma112ActualReciprocalTailIntegrand χ ψ s z
          (-((lemma23PaperL D ^ 9 : ℝ) : ℂ) + (v : ℂ) * I) * I)‖ ≤
      (2 * lemma44InverseSquareMass * Real.exp 2) * Real.exp (-(lemma23PaperL D ^ 10) / 4) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hm : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hab : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20 := neg_le_self (pow_nonneg h0.le 20)
  have hp : ∀ v ∈ uIoc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
      ‖lemma112ActualReciprocalTailIntegrand χ ψ s z
        (-((lemma23PaperL D ^ 9 : ℝ) : ℂ) + (v : ℂ) * I) * I‖ ≤
      lemma44InverseSquareMass * Real.exp (2 - lemma23PaperL D ^ 10 / 2) := by
    intro v hv
    rw [uIoc_of_le hab] at hv
    have hv' : |v| ≤ lemma23PaperL D ^ 20 := abs_le.mpr ⟨hv.1.le, hv.2⟩
    rw [norm_mul, norm_I, mul_one]
    have hp := lemma112_reciprocal_far_left_point_bound χ ψ hψ hD hL hs
      (w := -((lemma23PaperL D ^ 9 : ℝ) : ℂ) + (v : ℂ) * I)
      (by simp only [add_re, neg_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero])
      (by simpa only [add_im, neg_im, ofReal_im, neg_zero, zero_add, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero] using hv') hz
    simp only [add_im, neg_im, ofReal_im, neg_zero, zero_add, mul_im, ofReal_re,
      I_im, I_re, mul_one, mul_zero, add_zero] at hp
    apply hp.trans
    have he : Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v)) (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity :
      0 ≤ lemma44InverseSquareMass * Real.exp (2 - lemma23PaperL D ^ 10 / 2))
  apply (lemma112_normalized_integral_norm_le hp).trans
  calc
    _ = (2 * lemma44InverseSquareMass * Real.exp 2) *
        (lemma23PaperL D ^ 20 * Real.exp (-(lemma23PaperL D ^ 10) / 2)) := by
      rw [abs_of_nonneg (by positivity), show 2 - lemma23PaperL D ^ 10 / 2 =
        2 + -(lemma23PaperL D ^ 10) / 2 by ring, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (lemma61_far_left_integral_exponent_absorption (by linarith : 3 ≤ lemma23PaperL D)) (by positivity)

lemma lemma112_reciprocal_horizontal_integral_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    {z : ℝ} (hz : 1 / 2 ≤ z) {t : ℝ} (ht : |t| = lemma23PaperL D ^ 20) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ x : ℝ in -(lemma23PaperL D ^ 9)..(-1 : ℝ),
        lemma112ActualReciprocalTailIntegrand χ ψ s z ((x : ℂ) + (t : ℂ) * I))‖ ≤
      (lemma61QuarterSeriesMass * Real.exp 2) * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ h1
  have hm : 0 ≤ lemma61QuarterSeriesMass := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hab : -(lemma23PaperL D ^ 9) ≤ (-1 : ℝ) := by linarith only [h9]
  have hp : ∀ x ∈ uIoc (-(lemma23PaperL D ^ 9)) (-1 : ℝ),
      ‖lemma112ActualReciprocalTailIntegrand χ ψ s z ((x : ℂ) + (t : ℂ) * I)‖ ≤
        lemma61QuarterSeriesMass * Real.exp (2 + lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hb := lemma112_reciprocal_tail_point_bound χ ψ hψ hD hL hs
      (w := (x : ℂ) + (t : ℂ) * I) (by simpa using And.intro hx.1.le hx.2)
      (by simpa using ht.le) hz
    simp only [add_im, ofReal_im, zero_add, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero] at hb
    have he : t ^ 2 / (4 * lemma23PaperL D ^ 30) = lemma23PaperL D ^ 10 / 4 := by
      rw [← sq_abs t, ht]
      field_simp
    rw [neg_div, he] at hb
    apply hb.trans_eq
    rw [show 2 + lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
      (2 + lemma23PaperL D ^ 9) + -(lemma23PaperL D ^ 10 / 4) by ring]
    simp only [Real.exp_add]
    ring
  apply (lemma112_normalized_integral_norm_le hp).trans
  calc
    _ ≤ (lemma61QuarterSeriesMass * Real.exp (2 + lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) *
        lemma23PaperL D ^ 9 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_of_nonneg (by linarith only [h9])]
      linarith
    _ = (lemma61QuarterSeriesMass * Real.exp 2) * (lemma23PaperL D ^ 9 *
        Real.exp (lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      rw [show 2 + lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
        2 + (lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) by ring, Real.exp_add]
      ring
    _ ≤ (lemma61QuarterSeriesMass * Real.exp 2) * (lemma23PaperL D ^ 10 *
        Real.exp (1 + 4 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (pow_le_pow_right₀ h1 (by norm_num))
        (Real.exp_le_exp.mpr (by nlinarith only [pow_nonneg h0.le 9])) (Real.exp_nonneg _) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma61_right_gaussian_exponent_absorption hL) (by positivity)

lemma lemma112_reciprocal_tail_truncation_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    {z : ℝ} (hz : 1 / 2 ≤ z) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma112ActualReciprocalTailIntegrand χ ψ s z ((-1 : ℂ) + (v : ℂ) * I) * I)‖ ≤
      (2 * Real.exp 2 * (lemma44InverseSquareMass + lemma61QuarterSeriesMass)) *
        Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  let H := lemma23PaperL D ^ 20
  let a := -(lemma23PaperL D ^ 9)
  let F := lemma112ActualReciprocalTailIntegrand χ ψ s z
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let A := c * (∫ v : ℝ in -H..H, F ((-1 : ℂ) + (v : ℂ) * I) * I)
  let B := c * (∫ v : ℝ in -H..H, F ((a : ℂ) + (v : ℂ) * I) * I)
  let E := c * (∫ x : ℝ in a..(-1 : ℝ), F ((x : ℂ) - (H : ℂ) * I))
  let J := c * (∫ x : ℝ in a..(-1 : ℝ), F ((x : ℂ) + (H : ℂ) * I))
  have h0 : 0 < lemma23PaperL D := by linarith
  have hc := lemma112_reciprocal_tail_rectangle_cauchy χ ψ hψ (by linarith) hs z
  have he : A = B - E + J := by
    dsimp [A,B,E,J]
    simp only [intervalIntegral.integral_mul_const]
    unfold lemma44GeneralRectangleBoundaryIntegral at hc
    simp only [Complex.ofReal_neg,Complex.ofReal_one] at hc
    dsimp [H,a,F]
    simp only [Complex.ofReal_neg,Complex.ofReal_one]
    linear_combination c * hc
  have hb := lemma112_reciprocal_far_left_integral_bound χ ψ hψ hD hL hs hz
  have hm2 : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hb' : ‖B‖ ≤ (2 * lemma44InverseSquareMass * Real.exp 2) *
      Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    dsimp [B,c,F,a,H]
    simp only [Complex.ofReal_neg] at *
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * lemma44InverseSquareMass * Real.exp 2)
    apply Real.exp_le_exp.mpr
    have hpos : 0 ≤ lemma23PaperL D ^ 10 := by positivity
    linarith only [hpos]
  have hH : |H| = H := abs_of_pos (pow_pos h0 20)
  have hE := lemma112_reciprocal_horizontal_integral_bound χ ψ hψ hD hL hs hz (t := -H) (by simpa only [abs_neg] using hH)
  have hE' : ‖E‖ ≤ (lemma61QuarterSeriesMass * Real.exp 2) *
      Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    simpa only [E,c,F,a,H,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using hE
  have hJ := lemma112_reciprocal_horizontal_integral_bound χ ψ hψ hD hL hs hz (t := H) hH
  have hJ' : ‖J‖ ≤ (lemma61QuarterSeriesMass * Real.exp 2) *
      Real.exp (-(lemma23PaperL D ^ 10) / 8) := hJ
  change ‖A‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  have hN := norm_sub_le B E
  nlinarith only [hb',hE',hJ',hN]

end ZhangLS.Spec
