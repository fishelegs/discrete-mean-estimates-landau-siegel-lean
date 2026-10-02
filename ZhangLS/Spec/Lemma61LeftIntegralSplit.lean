import ZhangLS.Spec.Lemma61ReciprocalModel

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

lemma lemma61_actual_original_left_integrand_split {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s)
    {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) (-1 + (v : ℂ) * I) /
      (-1 + (v : ℂ) * I) =
      lemma61ReciprocalModelIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) +
      lemma61ActualZErrorIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) +
      lemma61ActualReciprocalTailIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) := by
  let w : ℂ := -1 + (v : ℂ) * I
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith)
  have hd := lemma61_large_shift_rectangle_bounds hL hs (w := w)
    ⟨by simpa [w] using neg_le_neg h9,by norm_num [w]⟩ (by simpa [w] using hv)
  have him : 0 < (s + w).im := by
    have h := (lemma61_wide_height_data hL hd.2.1).2.1
    linarith only [h]
  have hdual : 1 < (1 - s - w).re := by
    have h := (lemma61_region_real_parts hL hs).2
    simp [w]
    linarith only [h]
  unfold lemma61SingleMellinNumerator lemma61ReciprocalModelIntegrand
    lemma61ActualZErrorIntegrand lemma61ActualReciprocalTailIntegrand
  change DirichletCharacter.LFunction ψ (s + w) *
    exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) * lemma57OmegaOne D w / w = _
  rw [lemma61_actual_single_functional_equation ψ hψ him]
  have ha : 1 - (s + w) = 1 - s - w := by ring
  rw [ha,lemma61_actual_reciprocal_series_split ψ⁻¹ hdual]
  rw [← lemma61_model_Z_P4_factor ψ s w hL]
  ring

lemma lemma61_reciprocal_model_interval_integrable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D) (H : ℝ) :
    IntervalIntegrable (fun v : ℝ =>
      lemma61ReciprocalModelIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I) volume (-H) H := by
  simp_rw [lemma61_reciprocal_model_reflection ψ s]
  have hi := (lemma61_short_mellin_integrable ψ⁻¹ (1 - s) (lemma56PaperT D ^ 2) hD
    (by norm_num : (1 : ℝ) ≠ 0)).mul_const I
  exact (hi.comp_neg.const_mul (-lemma23DirichletZ ψ s)).intervalIntegrable

lemma lemma61_actual_left_tail_interval_integrable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s) :
    IntervalIntegrable (fun v : ℝ =>
      lemma61ActualReciprocalTailIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I)
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith)
  have hc := (lemma61_actual_reciprocal_tail_rectangle_differentiable ψ hψ hL hs).continuousOn
  have hm : MapsTo (fun v : ℝ => (-1 : ℂ) + (v : ℂ) * I)
      (uIcc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20))
      (lemma44ClosedRectangle (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20)) := by
    intro v hv
    rw [uIcc_of_le (neg_le_self (pow_nonneg h0.le 20))] at hv
    have ha : (-1 : ℝ) ∈ Icc (-(lemma23PaperL D ^ 9)) (-1) := ⟨by linarith only [h9],le_rfl⟩
    simpa [lemma44ClosedRectangle,mem_reProdIm] using And.intro ha hv
  exact ((hc.comp (by fun_prop) hm).mul continuousOn_const).intervalIntegrable

lemma lemma61_actual_original_left_integral_split {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma61InRegion D s) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        (lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) (-1 + (v : ℂ) * I) /
          (-1 + (v : ℂ) * I)) * I) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma61ReciprocalModelIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I) +
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma61ActualZErrorIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I) +
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma61ActualReciprocalTailIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hM := lemma61_reciprocal_model_interval_integrable ψ s hD (lemma23PaperL D ^ 20)
  have hE := (lemma61_error_vertical_interval_integrable ψ hL hs (a := -1) (by norm_num)).mul_const I
  simp only [Complex.ofReal_neg,Complex.ofReal_one] at hE
  have hT := lemma61_actual_left_tail_interval_integrable ψ hψ hL hs
  have he : (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      (lemma61SingleMellinNumerator (D := D) ψ s (lemma61PaperP4 D) (-1 + (v : ℂ) * I) /
        (-1 + (v : ℂ) * I)) * I) =
      ∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        (lemma61ReciprocalModelIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I +
          lemma61ActualZErrorIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I) +
          lemma61ActualReciprocalTailIntegrand (D := D) ψ s (-1 + (v : ℂ) * I) * I := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (neg_le_self (pow_nonneg h0.le 20))] at hv
    dsimp only
    rw [lemma61_actual_original_left_integrand_split ψ hψ hL hs (abs_le.mpr hv)]
    ring
  rw [he,intervalIntegral.integral_add (hM.add hE) hT,intervalIntegral.integral_add hM hE]
  ring

end ZhangLS.Spec
