import ZhangLS.Spec.Lemma53MellinBoundary
import ZhangLS.Spec.Lemma53OscillatoryEstimates

/-! # The actual inverse Mellin definition equals the oscillatory integral -/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma53_boundary_gamma_factor {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (((2 * Real.pi * x : ℝ) : ℂ) * I) ^ (-s) * Complex.Gamma s =
      (x : ℂ) ^ (-s) * lemma53PaperThetaStar s := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hA : 0 < 2 * Real.pi * x := mul_pos hπ hx
  have hzne : (((2 * Real.pi * x : ℝ) : ℂ) * I) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hA.ne') I_ne_zero
  unfold lemma53PaperThetaStar
  rw [Complex.cpow_def_of_ne_zero hzne, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hπ.ne'),
    Complex.log_ofReal_mul hA I_ne_zero, Complex.log_I,
    Real.log_mul hπ.ne' hx.ne', ← ofReal_log hx.le, ← ofReal_log hπ.le]
  have he : Complex.exp (((Real.log (2 * Real.pi) + Real.log x : ℝ) : ℂ) * (-s) +
        ((Real.pi : ℂ) / 2 * I) * (-s)) =
      Complex.exp ((Real.log x : ℂ) * (-s)) *
        Complex.exp ((Real.log (2 * Real.pi) : ℂ) * (-s)) *
          Complex.exp ((2 * Real.pi : ℂ) * I * (-s / 4)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexp : ((Real.log (2 * Real.pi) + Real.log x : ℝ) : ℂ) * (-s) +
      ((Real.pi : ℂ) / 2 * I) * (-s) =
      (((Real.log (2 * Real.pi) + Real.log x : ℝ) : ℂ) + (Real.pi : ℂ) / 2 * I) * (-s) := by ring
  rw [← hexp, he]
  ring

theorem lemma53_delta_one_eq_boundary {D : ℕ} {x : ℝ} (hx : 0 < x) :
    lemma53PaperDeltaOne D x =
      lemma53RegularizedMellin D (((2 * Real.pi * x : ℝ) : ℂ) * I) := by
  unfold lemma53PaperDeltaOne lemma53RegularizedMellin mellinInv lemma53MellinLine
  simp only [smul_eq_mul, Complex.real_smul, ofReal_div, ofReal_ofNat]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [lemma53_boundary_gamma_factor hx]
  ring

theorem lemma53_delta_one_oscillatory {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    lemma53PaperDeltaOne D x =
      ∫ u : ℝ, Complex.exp (lemma23PaperCenter D * (u : ℂ) -
        (lemma53PaperScale D : ℂ) ^ 2 * (u : ℂ) ^ 2 -
          (2 * Real.pi : ℂ) * I * (x : ℂ) * (Real.exp u : ℂ)) := by
  rw [lemma53_delta_one_eq_boundary hx,
    lemma53_boundary_mellin_exponential hD (by positivity : 0 < 2 * Real.pi * x)]
  unfold lemma53ExponentialKernel
  congr 1
  funext u
  congr 1
  push_cast
  ring

theorem lemma53_delta_one_log_gaussian {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    lemma53PaperDeltaOne D x =
      ∫ y : ℝ in Set.Ioi 0, Complex.exp ((lemma23PaperCenter D - 1) * (Real.log y : ℂ) -
        (lemma53PaperScale D : ℂ) ^ 2 * (Real.log y : ℂ) ^ 2 -
          (2 * Real.pi : ℂ) * I * (x : ℂ) * (y : ℂ)) := by
  rw [lemma53_exp_change_of_variables, lemma53_delta_one_oscillatory hD hx]
  congr 1
  funext u
  rw [Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

theorem lemma53_mellin_oscillatory_identity {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    lemma53PaperDelta D x = lemma53OscillatoryDelta D x := by
  unfold lemma53PaperDelta lemma53OscillatoryDelta
  rw [lemma53_delta_one_oscillatory hD hx, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with u
  unfold lemma53OscillatoryKernel
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  ring

theorem lemma53_paper_delta_norm_bound {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    ‖lemma53PaperDelta D x‖ ≤ Real.sqrt Real.pi / lemma53PaperScale D *
      Real.exp (1 / (16 * lemma53PaperScale D ^ 2)) := by
  rw [lemma53_mellin_oscillatory_identity hD hx]
  exact lemma53_oscillatory_delta_norm_bound hD x

end ZhangLS.Spec
