import ZhangLS.Spec.Lemma61ErrorHorizontalBounds

/-! # Actual original-left Z error for Lemma 6.1

The actual Z difference has a removable regular part at zero. Its
vertical integrability, exact shift to the reflected short-polynomial
line and horizontal budgets prove the original-left error <= C E1.
The full Lemma61Target remains unproved: finite polynomial Gaussian
relation, full horizontal L edges and final constants/thresholds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_E1_exponential_floor {D p : ℕ} (ψ : DirichletCharacter ℂ p) (s : ℂ) (k : ℝ) :
    Real.exp (-k * lemma23PaperL D ^ 10) ≤ lemma61ActualE1 D ψ s k := by
  have hL : 0 ≤ lemma23PaperL D := Real.log_natCast_nonneg D
  have hab := neg_le_self (pow_nonneg hL 20)
  have hi : 0 ≤ (∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
      ‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ * Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) := by
    apply intervalIntegral.integral_nonneg_of_forall hab
    intro v
    positivity
  unfold lemma61ActualE1
  nlinarith only [mul_nonneg (zpow_nonneg hL (-68 : ℤ)) hi]

lemma lemma61_actual_original_left_Z_error_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 64 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma61ActualZErrorIntegrand (D := D) ψ s ((-1 : ℂ) + (v : ℂ) * I) * I)‖ ≤
      (35 * Real.exp (246 * Real.pi + 1) + 16 * Real.exp (2 + 4 * Real.pi)) *
        lemma61ActualE1 D ψ s (1 / 8) := by
  let H := lemma23PaperL D ^ 20
  let a := 1 - 2 * s.re
  let F := lemma61ActualZErrorIntegrand (D := D) ψ s
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  have h0 : 0 < lemma23PaperL D := by linarith
  have he := lemma61_actual_error_line_shift ψ (by linarith) hs
  have hid : c * (∫ v : ℝ in -H..H, F ((-1 : ℂ) + (v : ℂ) * I) * I) =
      c * (∫ v : ℝ in -H..H, F (lemma61ErrorContourShift s v) * I) +
      c * (∫ x : ℝ in (-1 : ℝ)..a, F ((x : ℂ) - (H : ℂ) * I)) -
      c * (∫ x : ℝ in (-1 : ℝ)..a, F ((x : ℂ) + (H : ℂ) * I)) := by
    rw [he,mul_sub,mul_add]
  have hp := lemma61_actual_normalized_error_contour_bound ψ hψ (by linarith) hs (1 / 8 : ℝ)
  have hf := lemma61_E1_exponential_floor (D := D) ψ s (1 / 8 : ℝ)
  rw [show -(1 / 8 : ℝ) * lemma23PaperL D ^ 10 = -(lemma23PaperL D ^ 10) / 8 by ring] at hf
  have hH : |H| = H := abs_of_pos (pow_pos h0 20)
  have hb := lemma61_actual_horizontal_Z_error_integral_bound ψ hψ hL hs (t := -H) (by simpa only [abs_neg] using hH)
  have ht := lemma61_actual_horizontal_Z_error_integral_bound ψ hψ hL hs (t := H) hH
  have hb' : ‖c * (∫ x : ℝ in (-1 : ℝ)..a, F ((x : ℂ) - (H : ℂ) * I))‖ ≤
      (8 * Real.exp (2 + 4 * Real.pi)) * lemma61ActualE1 D ψ s (1 / 8) := by
    apply (show ‖c * (∫ x : ℝ in (-1 : ℝ)..a, F ((x : ℂ) - (H : ℂ) * I))‖ ≤
      (8 * Real.exp (2 + 4 * Real.pi)) * Real.exp (-(lemma23PaperL D ^ 10) / 8) by
        simpa only [c,F,a,H,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using hb).trans
    exact mul_le_mul_of_nonneg_left hf (by positivity)
  have ht' := ht.trans (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 8 * Real.exp (2 + 4 * Real.pi)))
  change ‖c * (∫ v : ℝ in -H..H, F ((-1 : ℂ) + (v : ℂ) * I) * I)‖ ≤ _
  rw [hid]
  apply (norm_sub_le _ _).trans
  have hn := norm_add_le (c * (∫ v : ℝ in -H..H, F (lemma61ErrorContourShift s v) * I))
    (c * (∫ x : ℝ in (-1 : ℝ)..a, F ((x : ℂ) - (H : ℂ) * I)))
  nlinarith only [hp,hb',ht',hn]

end ZhangLS.Spec
