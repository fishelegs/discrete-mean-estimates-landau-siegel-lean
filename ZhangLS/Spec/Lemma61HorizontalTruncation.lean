import ZhangLS.Spec.Lemma61HorizontalLBounds

/-! # Faithful original Lemma 6.1

Finite short-polynomial Gaussian inversion, actual original-left integral
decomposition and N approximation, actual full horizontal L edges and
uniform constants/thresholds yield lemma61_proved : Lemma61Target.
Original Psi, strict region and actual L/K/N/E1 are retained.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_actual_horizontal_L_point_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s w : ℂ} (hs : Lemma61InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 2) (hwi : |w.im| = lemma23PaperL D ^ 20) :
    ‖lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) w / w‖ ≤
      136 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ 519 *
        Real.exp (5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ h1
  have hp20 : 1 ≤ lemma23PaperL D ^ 20 := one_le_pow₀ h1
  have hwide : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 :=
    ⟨by linarith only [hwr.1,h9],hwr.2⟩
  have hn : 1 ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    linarith only [h,hwi,hp20]
  have hinv : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hsq : w.im ^ 2 = (lemma23PaperL D ^ 20) ^ 2 := by
    nlinarith only [sq_abs w.im,congrArg (fun x : ℝ => x ^ 2) hwi]
  have he : w.im ^ 2 / (4 * lemma23PaperL D ^ 30) = lemma23PaperL D ^ 10 / 4 := by
    rw [hsq]; field_simp
  have hG := lemma61_large_shift_gaussian_bound hL hwide
  rw [neg_div,he] at hG
  have hF := lemma61_actual_L_P4_rectangle_bound ψ hψ hL hs hwr hwi.le
  unfold lemma61SingleMellinNumerator
  simp only [norm_mul,norm_inv,div_eq_mul_inv]
  calc
    _ ≤ (136 * Real.exp (1 + 4 * Real.pi) * lemma23PaperL D ^ 519 *
        Real.exp (5 * lemma23PaperL D ^ 9)) *
        (Real.exp 1 * Real.exp (-(lemma23PaperL D ^ 10 / 4))) * 1 :=
      mul_le_mul (mul_le_mul (by simpa only [norm_mul] using hF) hG
        (norm_nonneg _) (by positivity)) hinv
        (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = _ := by
      change _ = 136 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ 519 *
        Real.exp (5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)
      rw [show 2 + 4 * Real.pi = (1 + 4 * Real.pi) + 1 by ring,
        show 5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
          5 * lemma23PaperL D ^ 9 + -(lemma23PaperL D ^ 10 / 4) by ring]
      simp only [Real.exp_add]; ring

lemma lemma61_horizontal_L_exponent_absorption {L : ℝ} (hL : 64 ≤ L) :
    L ^ 519 * Real.exp (5 * L ^ 9 - L ^ 10 / 4) ≤ Real.exp (-(L ^ 10) / 8) := by
  have h0 : 0 < L := by linarith
  have h8 : (519 : ℝ) ≤ L ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (by linarith : 3 ≤ L) 8
    norm_num at h
    linarith only [h]
  have hbudget : 519 * L ≤ L ^ 9 := by
    convert mul_le_mul_of_nonneg_right h8 h0.le using 1 <;> ring
  have hlog : Real.log (L ^ 519) ≤ L ^ 9 := by
    rw [Real.log_pow]
    norm_num
    have h := Real.log_le_sub_one_of_pos h0
    linarith only [h,hbudget]
  have h9 : 64 * L ^ 9 ≤ L ^ 10 := by
    convert mul_le_mul_of_nonneg_right hL (pow_nonneg h0.le 9) using 1 <;> ring
  calc
    _ ≤ Real.exp (L ^ 9) * Real.exp (5 * L ^ 9 - L ^ 10 / 4) :=
      mul_le_mul_of_nonneg_right (Real.le_exp_of_log_le hlog) (Real.exp_nonneg _)
    _ = Real.exp (L ^ 9 + (5 * L ^ 9 - L ^ 10 / 4)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [h9,pow_nonneg h0.le 9])

lemma lemma61_actual_horizontal_L_integral_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s)
    {t : ℝ} (ht : |t| = lemma23PaperL D ^ 20) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ x : ℝ in (-1 : ℝ)..2,
      lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) ((x : ℂ) + (t : ℂ) * I) /
        ((x : ℂ) + (t : ℂ) * I))‖ ≤
      408 * Real.exp (2 + 4 * Real.pi) * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 2)
    (f := fun x : ℝ => lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D)
      ((x : ℂ) + (t : ℂ) * I) / ((x : ℂ) + (t : ℂ) * I))
    (C := 136 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ 519 *
      Real.exp (5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4))
    (by
      intro x hx
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
      apply lemma61_actual_horizontal_L_point_bound ψ hψ (by linarith) hs
      · simpa using And.intro hx.1.le hx.2
      · simpa using ht)
  have hn := (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one
    (norm_nonneg (∫ x : ℝ in (-1 : ℝ)..2,
      lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) ((x : ℂ) + (t : ℂ) * I) /
        ((x : ℂ) + (t : ℂ) * I)))).trans (by simpa only [one_mul] using hb)
  rw [← norm_mul] at hn
  apply hn.trans
  calc
    _ = (408 * Real.exp (2 + 4 * Real.pi)) * (lemma23PaperL D ^ 519 *
        Real.exp (5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      norm_num only [sub_neg_eq_add,show (2 : ℝ) + 1 = 3 by norm_num,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma61_horizontal_L_exponent_absorption hL) (by positivity)

end ZhangLS.Spec
