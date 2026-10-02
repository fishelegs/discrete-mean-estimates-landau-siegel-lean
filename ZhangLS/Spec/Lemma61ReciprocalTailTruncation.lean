import ZhangLS.Spec.Lemma61ReciprocalTailRectangle

/-! # Actual reciprocal tail truncation for Lemma 6.1

The original n<T^3 finite sum and its n>=T^3 tail are split exactly.
Actual Gamma conductor growth cancels with actual P4, uniformly on the
wide high rectangle. Far-left and both horizontal tail integrals, the
actual local Cauchy relation and the original-left tail error are proved.
The full Lemma61Target remains unproved: finite polynomial error-line
shift, full horizontal edges and final constants/thresholds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def lemma61QuarterSeriesMass : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-5 / 4 : ℝ)

lemma lemma61_quarter_series_summable : Summable (fun n : ℕ => (n : ℝ) ^ (-5 / 4 : ℝ)) :=
  Real.summable_nat_rpow.mpr (by norm_num)

lemma lemma61_reciprocal_horizontal_term_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 3 ≤ lemma23PaperL D)
    {s w : ℂ} (hs : s.re ≤ 3 / 4) (hw : w.re ≤ -1) (n : ℕ) :
    ‖lemma61ReciprocalTailTerm D ψ (1 - s - w) n‖ *
      Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) ≤
        (n : ℝ) ^ (-5 / 4 : ℝ) * Real.exp ((w.re + 3) * Real.log (lemma56PaperT D)) := by
  by_cases hn0 : n = 0
  · simp [hn0,lemma61ReciprocalTailTerm]
  by_cases hcut : lemma56PaperT D ^ 3 ≤ (n : ℝ)
  swap
  · simp only [lemma61ReciprocalTailTerm,if_neg hcut,norm_zero,zero_mul]
    positivity
  have hnr : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
  have hlog : 3 * Real.log (lemma56PaperT D) ≤ Real.log (n : ℝ) := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (pow_pos (Real.exp_pos _) 3) hcut
  have he : -(1 - s - w).re = s.re + w.re - 1 := by simp; ring
  have hpe : (s.re + w.re - 1) * Real.log (n : ℝ) - 2 * w.re * Real.log (lemma56PaperT D) ≤
      (-5 / 4 : ℝ) * Real.log (n : ℝ) + (w.re + 3) * Real.log (lemma56PaperT D) := by
    have h1 := mul_le_mul_of_nonneg_right hs hnlog
    have h2 := mul_le_mul_of_nonpos_left hlog (by linarith only [hw] : w.re + 1 ≤ 0)
    nlinarith only [h1,h2]
  unfold lemma61ReciprocalTailTerm
  rw [if_pos hcut,lemma44_norm_LSeries_term_eq_real_exp _ _ hn0,he,Real.rpow_def_of_pos hnr]
  calc
    _ ≤ Real.exp ((s.re + w.re - 1) * Real.log (n : ℝ)) *
        Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) := by
      have hp := ψ.norm_le_one (n : ZMod p)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg ((s.re + w.re - 1) * Real.log (n : ℝ))))
        (Real.exp_nonneg (-2 * w.re * Real.log (lemma56PaperT D)))
    _ ≤ _ := by
      rw [← Real.exp_add,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hpe]

lemma lemma61_reciprocal_horizontal_sum_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 3 ≤ lemma23PaperL D)
    {s w : ℂ} (hs : s.re ≤ 3 / 4) (hw : w.re ≤ -1) :
    ‖∑' n : ℕ, lemma61ReciprocalTailTerm D ψ (1 - s - w) n‖ *
      Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) ≤
        lemma61QuarterSeriesMass * Real.exp ((w.re + 3) * Real.log (lemma56PaperT D)) := by
  have hz : 1 < (1 - s - w).re := by simp only [sub_re,one_re]; linarith only [hs,hw]
  have hnorm := summable_norm_iff.mpr (lemma61_reciprocal_tail_summable (D := D) ψ hz)
  have hscaled := hnorm.mul_right (Real.exp (-2 * w.re * Real.log (lemma56PaperT D)))
  have hmajor := lemma61_quarter_series_summable.mul_right
    (Real.exp ((w.re + 3) * Real.log (lemma56PaperT D)))
  calc
    _ ≤ (∑' n : ℕ, ‖lemma61ReciprocalTailTerm D ψ (1 - s - w) n‖) *
        Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) :=
      mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hnorm) (Real.exp_nonneg _)
    _ = ∑' n : ℕ, ‖lemma61ReciprocalTailTerm D ψ (1 - s - w) n‖ *
        Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) := (tsum_mul_right).symm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-5 / 4 : ℝ) * Real.exp ((w.re + 3) * Real.log (lemma56PaperT D)) :=
      hscaled.tsum_le_tsum (lemma61_reciprocal_horizontal_term_bound ψ hL hs hw) hmajor
    _ = _ := by rw [tsum_mul_right]; rfl

lemma lemma61_actual_horizontal_tail_point_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s w : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    (hwre : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ -1)
    (hwim : |w.im| = lemma23PaperL D ^ 20) :
    ‖lemma61ActualReciprocalTailIntegrand (D := D) ψ s w‖ ≤
      lemma61QuarterSeriesMass * Real.exp (2 + 4 * Real.pi + 2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hw : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 := ⟨hwre.1,by linarith only [hwre.2]⟩
  have hz := lemma61_actual_Z_P4_cancellation ψ hψ hL hs hw hwim.le
  have ho := lemma61_large_shift_gaussian_bound hL hw
  have hgauss : w.im ^ 2 / (4 * lemma23PaperL D ^ 30) = lemma23PaperL D ^ 10 / 4 := by
    rw [← sq_abs w.im,hwim]
    field_simp
  rw [neg_div,hgauss] at ho
  have hd := lemma61_large_shift_denominator_bound hwre.2
  have ht := lemma61_reciprocal_horizontal_sum_bound ψ⁻¹ hL (lemma61_region_quarter_bounds hL hs).2.le hwre.2
  have hT := lemma61_T_log_bounds hL
  have hT0 : 0 ≤ Real.log (lemma56PaperT D) := by linarith only [hT.1,hL]
  have he : (w.re + 3) * Real.log (lemma56PaperT D) ≤ 2 * lemma23PaperL D ^ 9 := by
    have hh := mul_le_mul_of_nonneg_right (show w.re + 3 ≤ 2 by linarith only [hwre.2]) hT0
    linarith only [hh,hT.2]
  have hm : 0 ≤ lemma61QuarterSeriesMass := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have ht' := ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hm)
  unfold lemma61ActualReciprocalTailIntegrand
  calc
    _ = ‖lemma23DirichletZ ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ *
        ‖∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n‖ * ‖lemma57OmegaOne D w‖ * ‖w‖⁻¹ := by
      simp only [div_eq_mul_inv,norm_mul,norm_inv]
      ring
    _ ≤ (Real.exp (1 + 4 * Real.pi) * Real.exp (-2 * w.re * Real.log (lemma56PaperT D))) *
        ‖∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n‖ *
        (Real.exp 1 * Real.exp (-(lemma23PaperL D ^ 10 / 4))) * 1 := by gcongr
    _ = Real.exp (2 + 4 * Real.pi) *
        (‖∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n‖ *
          Real.exp (-2 * w.re * Real.log (lemma56PaperT D))) * Real.exp (-(lemma23PaperL D ^ 10 / 4)) := by
      rw [show 2 + 4 * Real.pi = (1 + 4 * Real.pi) + 1 by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ Real.exp (2 + 4 * Real.pi) * (lemma61QuarterSeriesMass * Real.exp (2 * lemma23PaperL D ^ 9)) *
        Real.exp (-(lemma23PaperL D ^ 10 / 4)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht' (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by
      rw [show 2 + 4 * Real.pi + 2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
        (2 + 4 * Real.pi) + 2 * lemma23PaperL D ^ 9 + -(lemma23PaperL D ^ 10 / 4) by ring]
      simp only [Real.exp_add]
      ring

lemma lemma61_actual_horizontal_tail_integral_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 64 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    {t : ℝ} (ht : |t| = lemma23PaperL D ^ 20) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ x : ℝ in -(lemma23PaperL D ^ 9)..(-1 : ℝ),
        lemma61ActualReciprocalTailIntegrand (D := D) ψ s ((x : ℂ) + (t : ℂ) * I))‖ ≤
      (lemma61QuarterSeriesMass * Real.exp (2 + 4 * Real.pi)) *
        Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hm : 0 ≤ lemma61QuarterSeriesMass := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hab : -(lemma23PaperL D ^ 9) ≤ (-1 : ℝ) := by linarith only [h9]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(lemma23PaperL D ^ 9)) (b := (-1 : ℝ))
    (f := fun x : ℝ => lemma61ActualReciprocalTailIntegrand (D := D) ψ s ((x : ℂ) + (t : ℂ) * I))
    (C := lemma61QuarterSeriesMass * Real.exp (2 + 4 * Real.pi + 2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4))
    (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      apply lemma61_actual_horizontal_tail_point_bound ψ hψ (by linarith) hs
      · simpa using And.intro hx.1.le hx.2
      · simpa using ht)
  have hn := (mul_le_mul_of_nonneg_right lemma61_mellin_normalization_norm_le_one
    (norm_nonneg (∫ x : ℝ in -(lemma23PaperL D ^ 9)..(-1 : ℝ),
      lemma61ActualReciprocalTailIntegrand (D := D) ψ s ((x : ℂ) + (t : ℂ) * I)))).trans (by simpa only [one_mul] using hb)
  rw [← norm_mul] at hn
  apply hn.trans
  calc
    _ ≤ (lemma61QuarterSeriesMass * Real.exp (2 + 4 * Real.pi + 2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) *
        lemma23PaperL D ^ 9 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_of_nonneg (by linarith only [h9])]
      linarith
    _ = (lemma61QuarterSeriesMass * Real.exp (2 + 4 * Real.pi)) *
        (lemma23PaperL D ^ 9 * Real.exp (2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      rw [show 2 + 4 * Real.pi + 2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
        (2 + 4 * Real.pi) + (2 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ (lemma61QuarterSeriesMass * Real.exp (2 + 4 * Real.pi)) *
        (lemma23PaperL D ^ 10 * Real.exp (1 + 4 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul (pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
        (Real.exp_le_exp.mpr (by nlinarith only [pow_nonneg h0.le 9]))
        (Real.exp_nonneg _) (pow_nonneg h0.le 10)
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma61_right_gaussian_exponent_absorption hL) (by positivity)

lemma lemma61_actual_reciprocal_tail_truncation_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 64 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ActualReciprocalTailIntegrand (D := D) ψ s ((-1 : ℂ) + (v : ℂ) * I) * I)‖ ≤
      (2 * Real.exp (2 + 4 * Real.pi) * (lemma44InverseSquareMass + lemma61QuarterSeriesMass)) *
        Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  let H := lemma23PaperL D ^ 20
  let a := -(lemma23PaperL D ^ 9)
  let F := lemma61ActualReciprocalTailIntegrand (D := D) ψ s
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let A := c * (∫ v : ℝ in -H..H, F ((-1 : ℂ) + (v : ℂ) * I) * I)
  let B := c * (∫ v : ℝ in -H..H, F ((a : ℂ) + (v : ℂ) * I) * I)
  let E := c * (∫ x : ℝ in a..(-1 : ℝ), F ((x : ℂ) - (H : ℂ) * I))
  let J := c * (∫ x : ℝ in a..(-1 : ℝ), F ((x : ℂ) + (H : ℂ) * I))
  have h0 : 0 < lemma23PaperL D := by linarith
  have hc := lemma61_actual_reciprocal_tail_rectangle_cauchy ψ hψ (by linarith) hs
  have he : A = B - E + J := by
    dsimp [A,B,E,J]
    simp only [intervalIntegral.integral_mul_const]
    unfold lemma44GeneralRectangleBoundaryIntegral at hc
    simp only [Complex.ofReal_neg,Complex.ofReal_one] at hc
    dsimp [H,a,F]
    simp only [Complex.ofReal_neg,Complex.ofReal_one]
    linear_combination c * hc
  have hb := lemma61_actual_far_left_tail_integral_bound ψ hψ (by linarith) hs
  have hm2 : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hb' : ‖B‖ ≤ (2 * lemma44InverseSquareMass * Real.exp (2 + 4 * Real.pi)) *
      Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    dsimp [B,c,F,a,H]
    simp only [Complex.ofReal_neg] at *
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * lemma44InverseSquareMass * Real.exp (2 + 4 * Real.pi))
    apply Real.exp_le_exp.mpr
    have hpos : 0 ≤ lemma23PaperL D ^ 10 := by positivity
    linarith only [hpos]
  have hH : |H| = H := abs_of_pos (pow_pos h0 20)
  have hE := lemma61_actual_horizontal_tail_integral_bound ψ hψ hL hs (t := -H) (by simpa only [abs_neg] using hH)
  have hE' : ‖E‖ ≤ (lemma61QuarterSeriesMass * Real.exp (2 + 4 * Real.pi)) *
      Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
    simpa only [E,c,F,a,H,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using hE
  have hJ := lemma61_actual_horizontal_tail_integral_bound ψ hψ hL hs (t := H) hH
  have hJ' : ‖J‖ ≤ (lemma61QuarterSeriesMass * Real.exp (2 + 4 * Real.pi)) *
      Real.exp (-(lemma23PaperL D ^ 10) / 8) := hJ
  change ‖A‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  have hN := norm_sub_le B E
  nlinarith only [hb',hE',hJ',hN]

end ZhangLS.Spec
