import ZhangLS.Spec.Lemma61ActualZError
import ZhangLS.Spec.Lemma44LocalRectangle
import ZhangLS.Spec.Lemma61ReciprocalTailKernel

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

lemma lemma61_positive_real_cpow_model {B : ℝ} (hB : 0 < B) (w : ℂ) :
    (B : ℂ) ^ (-w) = exp (-(Real.log B : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hB.ne'),← Complex.ofReal_log hB.le]
  congr 1
  ring

noncomputable def lemma61ErrorDifferenceNumerator {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s w : ℂ) : ℂ :=
  lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
    ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)

noncomputable def lemma61ErrorRegularIntegrand {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s w : ℂ) : ℂ :=
  dslope (lemma61ErrorDifferenceNumerator (D := D) ψ s) 0 w *
    lemma61ShortPolynomial D ψ⁻¹ (1 - s - w) *
      exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) * lemma57OmegaOne D w

lemma lemma61_error_difference_at_zero {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma61ErrorDifferenceNumerator (D := D) ψ s 0 = 0 := by
  simp [lemma61ErrorDifferenceNumerator]

lemma lemma61_error_regular_eq_actual_of_ne_zero {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) {w : ℂ} (hw : w ≠ 0) :
    lemma61ErrorRegularIntegrand (D := D) ψ s w = lemma61ActualZErrorIntegrand (D := D) ψ s w := by
  unfold lemma61ErrorRegularIntegrand
  rw [dslope_of_ne _ hw,slope_def_field,lemma61_error_difference_at_zero]
  simp only [sub_zero]
  rfl

lemma lemma61_error_difference_rectangle_differentiable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    DifferentiableOn ℂ (lemma61ErrorDifferenceNumerator (D := D) ψ s)
      (lemma44ClosedRectangle (-1) 1 (lemma23PaperL D ^ 20)) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hbase : 0 < lemma23PaperP D * lemma51PaperT0 D := mul_pos (Real.exp_pos _) (pow_pos h0 519)
  have hmodel : Differentiable ℂ (fun w : ℂ =>
      ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) := by
    simp_rw [lemma61_positive_real_cpow_model hbase]
    fun_prop
  intro w hw
  change w.re ∈ Icc (-1) 1 ∧ w.im ∈ Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) at hw
  have hpow : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hh : |(s + w).im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3 := by
    have he : (s + w).im - (lemma23PaperCenter D).im = (s.im - (lemma23PaperCenter D).im) + w.im := by simp; ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hs.2,abs_le.mpr hw.2,hpow])
  have hdata := lemma61_wide_height_data hL hh
  have hzi : 0 < (s + w).im := by linarith only [hdata.2.1]
  have hz : DifferentiableAt ℂ (fun u : ℂ => lemma23DirichletZ ψ (s + u)) w :=
    (lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ hzi.ne').comp w (by fun_prop)
  exact (hz.sub ((hmodel w).const_mul (lemma23DirichletZ ψ s))).differentiableWithinAt

lemma lemma61_error_regular_rectangle_differentiable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    DifferentiableOn ℂ (lemma61ErrorRegularIntegrand (D := D) ψ s)
      (lemma44ClosedRectangle (-1) 1 (lemma23PaperL D ^ 20)) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hn : lemma44ClosedRectangle (-1) 1 (lemma23PaperL D ^ 20) ∈ nhds (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds]
    simp only [lemma44ClosedRectangle,interior_reProdIm,interior_Icc,mem_reProdIm,mem_Ioo,zero_re,zero_im]
    constructor <;> constructor <;> norm_num <;> positivity
  have hd := (Complex.differentiableOn_dslope hn).2 (lemma61_error_difference_rectangle_differentiable ψ hL hs)
  have hN := lemma61_short_polynomial_differentiable (D := D) ψ⁻¹
  have hp : Differentiable ℂ (fun w : ℂ => lemma61ShortPolynomial D ψ⁻¹ (1 - s - w) *
      exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) * lemma57OmegaOne D w) := by
    unfold lemma57OmegaOne
    fun_prop
  convert hd.mul hp.differentiableOn using 1
  funext w
  dsimp [lemma61ErrorRegularIntegrand]
  ring

end ZhangLS.Spec
