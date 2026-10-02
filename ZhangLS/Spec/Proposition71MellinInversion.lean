import ZhangLS.Spec.Lemma54
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Actual Mellin inversion for the Section 7 Δ kernel

The inversion uses the actual Δ, its actual Mellin transform δ, its proved
continuity and Mellin convergence, and a proved vertical integrability bound.
No Mellin inversion or interchange estimate is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Topology
set_option maxHeartbeats 2000000

/-- Absolute integrability on every vertical line σ≥1/2 follows from the actual
second-derivative moment, without an assumed decay bound. -/
theorem proposition71_actual_delta_vertical_integrable {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {σ : ℝ} (hσ : 1/2≤σ) :
    VerticalIntegrable (lemma54PaperDeltaMellin D) σ := by
  have hσp : 0<σ := by linarith
  have hcont : Continuous (fun t : ℝ => lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((lemma54_mellin_analyticOnNhd hD hL) _ (by simpa using hσp)).continuousAt.comp
      (by fun_prop)
  have hM : 0≤lemma54SecondMoment D σ := lemma54_actual_second_moment_nonneg D
  have hbound (t : ℝ) :
      ‖lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I)‖ ≤
        4*lemma54SecondMoment D σ*(1+t^2)⁻¹ := by
    have hb := lemma54_actual_mellin_norm_bound_by_second_moment hD hL
      (s := (σ : ℂ)+(t : ℂ)*I) (by simpa using hσp)
    have hn : ‖(σ : ℂ)+(t : ℂ)*I‖^2=σ^2+t^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp [pow_two]
    simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero] at hb
    rw [hn] at hb
    apply hb.trans
    rw [←div_eq_mul_inv]
    apply (div_le_div_iff₀ (by nlinarith [sq_nonneg t] : 0<σ^2+t^2)
      (by positivity : 0<1+t^2)).mpr
    have hd : 1+t^2≤4*(σ^2+t^2) := by nlinarith [sq_nonneg t]
    nlinarith [mul_le_mul_of_nonneg_left hd hM]
  exact (integrable_inv_one_add_sq.const_mul (4*lemma54SecondMoment D σ)).mono'
    hcont.aestronglyMeasurable (ae_of_all _ hbound)

/-- The actual inversion bridge for (7.14) and (7.19). -/
theorem proposition71_actual_delta_mellin_inversion {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {σ x : ℝ}
    (hσ : 1/2≤σ) (hx : 0<x) :
    mellinInv σ (lemma54PaperDeltaMellin D) x=lemma53PaperDelta D x := by
  apply mellinInv_mellin_eq σ (lemma53PaperDelta D) hx
  · exact lemma54_mellin_convergent hD hL (by simpa using (show 0<σ by linarith))
  · exact proposition71_actual_delta_vertical_integrable hD hL hσ
  · exact (lemma54_actual_delta_hasDerivAt hD hx).continuousAt

/-- Expanded normalized vertical integral; the argument l/(phr) is still
present in full and no hr factor has been dropped. -/
theorem proposition71_actual_scaled_delta_mellin {D : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {σ p h r l : ℝ}
    (hσ : 1/2≤σ) (hp : 0<p) (hh : 0<h) (hr : 0<r) (hl : 0<l) :
    lemma53PaperDelta D (l/(p*h*r))=
      ((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ,
        ((l/(p*h*r) : ℝ) : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))*
          lemma54PaperDeltaMellin D ((σ : ℂ)+(t : ℂ)*I) := by
  rw [←proposition71_actual_delta_mellin_inversion hD hL hσ (by positivity : 0<l/(p*h*r))]
  simp only [mellinInv,smul_eq_mul,Complex.real_smul]

end ZhangLS.Spec
