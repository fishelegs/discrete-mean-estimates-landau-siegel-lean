import ZhangLS.Spec.Lemma112ReciprocalModel
/-! # Exact decomposition of the actual original left contour -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_actual_original_left_integrand_split {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (z : ℝ) (hψ : Lemma23InPsi (D := D) ψ)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma112InRegion D s)
    {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s (lemma23PaperP D ^ z) (-1 + (v : ℂ) * I) /
      (-1 + (v : ℂ) * I) =
      lemma112ReciprocalModelIntegrand χ ψ s z (-1 + (v : ℂ) * I) +
      lemma112ActualZErrorIntegrand χ ψ s z (-1 + (v : ℂ) * I) +
      lemma112ActualReciprocalTailIntegrand χ ψ s z (-1 + (v : ℂ) * I) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let w : ℂ := -1 + (v : ℂ) * I
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith)
  have hd := lemma61_large_shift_rectangle_bounds hL (lemma112_region_subset_lemma61 hL hs) (w := w)
    ⟨by simpa [w] using neg_le_neg h9,by norm_num [w]⟩ (by simpa [w] using hv)
  have him : 0 < (s + w).im := by
    have h := (lemma61_wide_height_data hL hd.2.1).2.1
    linarith only [h]
  have hdual : 1 < (1 - s - w).re := by
    norm_num [w, hs.1]
  unfold lemma61SingleMellinNumerator lemma112ReciprocalModelIntegrand
    lemma112ActualZErrorIntegrand lemma112ActualReciprocalTailIntegrand lemma112ErrorDifferenceNumerator
  change DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (s + w) *
    exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) * lemma57OmegaOne D w / w = _
  rw [lemma112_actual_twist_functional_equation χ ψ hL hψ him]
  have ha : 1 - (s + w) = 1 - s - w := by ring
  rw [ha,lemma112_actual_reciprocal_series_split χ ψ⁻¹ hdual]
  rw [← lemma112_model_scale_identity χ ψ hD s w z]
  ring

lemma lemma112_reciprocal_model_interval_integrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (z : ℝ) (s : ℂ) (hD : 1 < D) (H : ℝ) :
    IntervalIntegrable (fun v : ℝ =>
      lemma112ReciprocalModelIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I) volume (-H) H := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  simp_rw [lemma112_reciprocal_model_reflection χ ψ s z]
  have hi := (lemma112_short_mellin_integrable χ ψ⁻¹ (1 - s) (lemma112DualScale D z) hD
    (by norm_num : (1 : ℝ) ≠ 0)).mul_const I
  exact (hi.comp_neg.const_mul (-lemma23DirichletZ (lemma44CharacterTwist χ ψ) s)).intervalIntegrable

lemma lemma112_actual_left_tail_interval_integrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (z : ℝ) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma112InRegion D s) :
    IntervalIntegrable (fun v : ℝ =>
      lemma112ActualReciprocalTailIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I)
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have h0 : 0 < lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith)
  have hc := (lemma112_reciprocal_tail_rectangle_differentiable χ ψ hψ hL hs z).continuousOn
  have hm : MapsTo (fun v : ℝ => (-1 : ℂ) + (v : ℂ) * I)
      (uIcc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20))
      (lemma44ClosedRectangle (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20)) := by
    intro v hv
    rw [uIcc_of_le (neg_le_self (pow_nonneg h0.le 20))] at hv
    have ha : (-1 : ℝ) ∈ Icc (-(lemma23PaperL D ^ 9)) (-1) := ⟨by linarith only [h9],le_rfl⟩
    simpa [lemma44ClosedRectangle,mem_reProdIm] using And.intro ha hv
  exact ((hc.comp (by fun_prop) hm).mul continuousOn_const).intervalIntegrable

lemma lemma112_actual_original_left_integral_split {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (z : ℝ) (hψ : Lemma23InPsi (D := D) ψ)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma112InRegion D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        (lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s (lemma23PaperP D ^ z) (-1 + (v : ℂ) * I) /
          (-1 + (v : ℂ) * I)) * I) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma112ReciprocalModelIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I) +
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma112ActualZErrorIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I) +
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
          lemma112ActualReciprocalTailIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have h0 : 0 < lemma23PaperL D := by linarith
  have hM := lemma112_reciprocal_model_interval_integrable χ ψ z s hD (lemma23PaperL D ^ 20)
  have hE := (lemma112_error_vertical_interval_integrable χ ψ hD hL hs z (a := -1) (by norm_num)).mul_const I
  simp only [Complex.ofReal_neg,Complex.ofReal_one] at hE
  have hT := lemma112_actual_left_tail_interval_integrable χ ψ z hψ hL hs
  have he : (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      (lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s (lemma23PaperP D ^ z) (-1 + (v : ℂ) * I) /
        (-1 + (v : ℂ) * I)) * I) =
      ∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        (lemma112ReciprocalModelIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I +
          lemma112ActualZErrorIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I) +
          lemma112ActualReciprocalTailIntegrand χ ψ s z (-1 + (v : ℂ) * I) * I := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (neg_le_self (pow_nonneg h0.le 20))] at hv
    dsimp only
    rw [lemma112_actual_original_left_integrand_split χ ψ z hψ hD hL hs (abs_le.mpr hv)]
    ring
  rw [he,intervalIntegral.integral_add (hM.add hE) hT,intervalIntegral.integral_add hM hE]
  ring

end ZhangLS.Spec
