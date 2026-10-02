import ZhangLS.Spec.Lemma61ErrorRegularPart

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

lemma lemma61_error_vertical_ae_eq {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (a : ℝ) :
    (fun v : ℝ => lemma61ErrorRegularIntegrand (D := D) ψ s ((a : ℂ) + (v : ℂ) * I)) =ᵐ[volume]
      (fun v : ℝ => lemma61ActualZErrorIntegrand (D := D) ψ s ((a : ℂ) + (v : ℂ) * I)) := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with v hv
  apply lemma61_error_regular_eq_actual_of_ne_zero
  intro he
  have hi := congrArg Complex.im he
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add,zero_im] at hi
  exact hv hi

lemma lemma61_error_vertical_interval_integrable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    {a : ℝ} (ha : a ∈ Icc (-1) 1) :
    IntervalIntegrable (fun v : ℝ => lemma61ActualZErrorIntegrand (D := D) ψ s ((a : ℂ) + (v : ℂ) * I))
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hR := (lemma61_error_regular_rectangle_differentiable ψ hL hs).continuousOn
  have hm : MapsTo (fun v : ℝ => (a : ℂ) + (v : ℂ) * I)
      (uIcc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20))
      (lemma44ClosedRectangle (-1) 1 (lemma23PaperL D ^ 20)) := by
    intro v hv
    rw [uIcc_of_le (neg_le_self (pow_nonneg h0.le 20))] at hv
    simpa [lemma44ClosedRectangle,mem_reProdIm] using And.intro ha hv
  have hi : IntervalIntegrable (fun v : ℝ => lemma61ErrorRegularIntegrand (D := D) ψ s ((a : ℂ) + (v : ℂ) * I))
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) :=
    (hR.comp (by fun_prop) hm).intervalIntegrable
  exact hi.congr_ae (ae_restrict_of_ae (lemma61_error_vertical_ae_eq ψ s a))

lemma lemma61_error_vertical_integral_eq {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (a H : ℝ) :
    (∫ v : ℝ in -H..H, lemma61ErrorRegularIntegrand (D := D) ψ s ((a : ℂ) + (v : ℂ) * I) * I) =
      (∫ v : ℝ in -H..H, lemma61ActualZErrorIntegrand (D := D) ψ s ((a : ℂ) + (v : ℂ) * I) * I) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [lemma61_error_vertical_ae_eq ψ s a] with v hv
  intro _
  exact congrArg (fun z : ℂ => z * I) hv

lemma lemma61_actual_error_path_interval_integrable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    IntervalIntegrable (fun v : ℝ => lemma61ActualZErrorIntegrand (D := D) ψ s (lemma61ErrorContourShift s v))
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  have hr := lemma61_region_real_parts hL hs
  have ha : (1 - 2 * s.re : ℝ) ∈ Icc (-1) 1 := ⟨by linarith only [hr.2],by linarith only [hr.1]⟩
  simpa only [lemma61ErrorContourShift,mul_comm] using lemma61_error_vertical_interval_integrable ψ hL hs ha

lemma lemma61_error_regular_path_rectangle_cauchy {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    lemma44GeneralRectangleBoundaryIntegral (lemma61ErrorRegularIntegrand (D := D) ψ s)
      (-1) (1 - 2 * s.re) (lemma23PaperL D ^ 20) = 0 := by
  have hr := lemma61_region_real_parts hL hs
  have h0 : 0 < lemma23PaperL D := by linarith
  apply lemma44_local_rectangle_cauchy _ (by linarith only [hr.2]) (by positivity)
  apply (lemma61_error_regular_rectangle_differentiable ψ hL hs).mono
  intro w hw
  exact ⟨⟨hw.1.1,by linarith only [hw.1.2,hr.1]⟩,hw.2⟩

lemma lemma61_actual_error_line_shift {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma61ActualZErrorIntegrand (D := D) ψ s ((-1 : ℂ) + (v : ℂ) * I) * I) =
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma61ActualZErrorIntegrand (D := D) ψ s (lemma61ErrorContourShift s v) * I) +
      (∫ x : ℝ in (-1 : ℝ)..(1 - 2 * s.re),
        lemma61ActualZErrorIntegrand (D := D) ψ s ((x : ℂ) - ((lemma23PaperL D ^ 20 : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in (-1 : ℝ)..(1 - 2 * s.re),
        lemma61ActualZErrorIntegrand (D := D) ψ s ((x : ℂ) + ((lemma23PaperL D ^ 20 : ℝ) : ℂ) * I)) := by
  let H := lemma23PaperL D ^ 20
  let a := 1 - 2 * s.re
  let R := lemma61ErrorRegularIntegrand (D := D) ψ s
  let F := lemma61ActualZErrorIntegrand (D := D) ψ s
  have h0 : 0 < H := by dsimp [H]; positivity
  have hb : (∫ x : ℝ in (-1 : ℝ)..a, R ((x : ℂ) - (H : ℂ) * I)) =
      (∫ x : ℝ in (-1 : ℝ)..a, F ((x : ℂ) - (H : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply lemma61_error_regular_eq_actual_of_ne_zero
    intro he
    have hi := congrArg Complex.im he
    simp only [sub_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_im] at hi
    linarith only [hi,h0]
  have ht : (∫ x : ℝ in (-1 : ℝ)..a, R ((x : ℂ) + (H : ℂ) * I)) =
      (∫ x : ℝ in (-1 : ℝ)..a, F ((x : ℂ) + (H : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply lemma61_error_regular_eq_actual_of_ne_zero
    intro he
    have hi := congrArg Complex.im he
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add,zero_im] at hi
    linarith only [hi,h0]
  have hc := lemma61_error_regular_path_rectangle_cauchy ψ hL hs
  unfold lemma44GeneralRectangleBoundaryIntegral at hc
  simp only [Complex.ofReal_neg,Complex.ofReal_one] at hc
  have hleft := lemma61_error_vertical_integral_eq (D := D) ψ s (-1) H
  simp only [Complex.ofReal_neg,Complex.ofReal_one] at hleft
  rw [← hleft,
    show (fun v : ℝ => F (lemma61ErrorContourShift s v) * I) =
      (fun v : ℝ => F ((a : ℂ) + (v : ℂ) * I) * I) by funext v; simp [lemma61ErrorContourShift,a,mul_comm],
    ← lemma61_error_vertical_integral_eq (D := D) ψ s a H]
  change (∫ v : ℝ in -H..H, R ((-1 : ℂ) + (v : ℂ) * I) * I) =
    (∫ v : ℝ in -H..H, R ((a : ℂ) + (v : ℂ) * I) * I) + _ - _
  rw [← hb,← ht]
  simp only [intervalIntegral.integral_mul_const]
  linear_combination -hc

end ZhangLS.Spec
