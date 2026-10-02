import ZhangLS.Spec.Lemma61ErrorContourKernel

/-! # Actual wide Gamma and original E1 error estimates for Lemma 6.1

Actual Gamma recurrence gives sharp all-real-part logarithmic derivatives.
Original Psi implies actual wide normalized Z bounds and small complex shifts.
The shifted contour gives the original short sum and its original E1 bound.
The full Lemma61Target remains unproved: contour and truncation relations remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Topology ComplexConjugate
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def lemma61ActualZErrorIntegrand {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s w : ℂ) : ℂ :=
  ((lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
    ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w) *
      lemma61ShortPolynomial D ψ⁻¹ (1 - s - w) *
        exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) * lemma57OmegaOne D w

lemma lemma61_actual_error_contour_point_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma61ActualZErrorIntegrand (D := D) ψ s (lemma61ErrorContourShift s v)‖ ≤
      (35 * Real.exp (246 * Real.pi + 1)) * lemma23PaperL D ^ (-68 : ℤ) *
        (‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ *
          Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) := by
  have hw := lemma61_error_contour_bounds hs hv
  have hz := lemma61_actual_complex_Z_shift ψ hψ hL hs hw.1 hw.2
  have hp := lemma61_P4_exponential_thin_bound hL hw.1
  have ho : ‖lemma57OmegaOne D (lemma61ErrorContourShift s v)‖ ≤ Real.exp 1 *
      Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
    simpa [lemma61ErrorContourShift] using lemma61_omega_one_thin_gaussian_bound hL hw.1
  unfold lemma61ActualZErrorIntegrand
  rw [norm_mul,norm_mul,norm_mul,lemma61_error_contour_short_norm]
  calc
    _ ≤ ((35 * Real.exp (238 * Real.pi)) * lemma23PaperL D ^ (-68 : ℤ)) *
        ‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ * Real.exp (8 * Real.pi) *
        (Real.exp 1 * Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) := by
      gcongr
    _ = _ := by
      rw [show 246 * Real.pi + 1 = 238 * Real.pi + (8 * Real.pi + 1) by ring,
        Real.exp_add,Real.exp_add]
      ring

lemma lemma61_actual_error_contour_integral_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) (k : ℝ) :
    ‖∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
      lemma61ActualZErrorIntegrand (D := D) ψ s (lemma61ErrorContourShift s v) * I‖ ≤
        (35 * Real.exp (246 * Real.pi + 1)) * lemma61ActualE1 D ψ s k := by
  let C : ℝ := 35 * Real.exp (246 * Real.pi + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hab : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20 := neg_le_self (pow_nonneg hL0.le _)
  have hpoint : ∀ᵐ v : ℝ ∂volume, v ∈ Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) →
      ‖lemma61ActualZErrorIntegrand (D := D) ψ s (lemma61ErrorContourShift s v) * I‖ ≤
        (C * lemma23PaperL D ^ (-68 : ℤ)) *
          (‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ *
            Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) := by
    apply Filter.Eventually.of_forall
    intro v hv
    have ha : |v| ≤ lemma23PaperL D ^ 20 := abs_le.mpr ⟨hv.1.le,hv.2⟩
    simpa only [norm_mul,norm_I,mul_one,C] using lemma61_actual_error_contour_point_bound ψ hψ hL hs ha
  have hint : IntervalIntegrable (fun v : ℝ =>
      (C * lemma23PaperL D ^ (-68 : ℤ)) *
        (‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ *
          Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))))
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) :=
    (lemma61_error_integrand_interval_integrable ψ s).const_mul _
  have hb := intervalIntegral.norm_integral_le_of_norm_le hab hpoint hint
  rw [intervalIntegral.integral_const_mul] at hb
  change _ ≤ C * lemma61ActualE1 D ψ s k
  unfold lemma61ActualE1
  have he := Real.exp_pos (-k * lemma23PaperL D ^ 10)
  nlinarith only [hb,he,hC]

lemma lemma61_actual_normalized_error_contour_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) (k : ℝ) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
        lemma61ActualZErrorIntegrand (D := D) ψ s (lemma61ErrorContourShift s v) * I)‖ ≤
          (35 * Real.exp (246 * Real.pi + 1)) * lemma61ActualE1 D ψ s k := by
  have hb := lemma61_actual_error_contour_integral_bound ψ hψ hL hs k
  have hn : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ ≤ 1 := by
    have hbase : 1 ≤ ‖2 * (Real.pi : ℂ) * I‖ := by
      rw [norm_mul,norm_mul,norm_I,mul_one,Complex.norm_of_nonneg Real.pi_pos.le]
      norm_num
      linarith [Real.one_le_pi_div_two]
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hbase
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (by simpa using hb)

end ZhangLS.Spec
