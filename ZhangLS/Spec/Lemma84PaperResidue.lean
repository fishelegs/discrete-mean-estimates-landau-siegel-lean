import ZhangLS.Spec.Lemma84Residue
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1000000

lemma lemma84_smoothing_beta_norm {D : ℕ} (μ : ℕ)
    (hα : 0 < lemma44PaperAlpha D) :
    0 < ‖lemma84SmoothingBeta D μ‖ ∧
      ‖lemma84SmoothingBeta D μ‖ ≤ 3*lemma44PaperAlpha D := by
  unfold lemma84SmoothingBeta
  split_ifs <;>
    norm_num [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hα] <;> constructor <;> linarith

lemma lemma84_positive_cpow_eq_exp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ)^s = exp (s*(Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
  congr 1
  ring

/-- The displayed G is exactly the model contour integral, with the source's
cyclic β shifts and both smoothing shifts. -/
lemma lemma84_paper_model_circle_integral (D : ℕ) (c : ℝ) (j : Fin 3) (μ : ℕ)
    {x : ℝ} (hx : 0 < x) (hα : 0 < lemma44PaperAlpha D) :
    (2*Real.pi*I : ℂ)⁻¹ * circleIntegral (fun s : ℂ =>
      (s+lemma83PaperBeta D c (j+1))*(s+lemma83PaperBeta D c (j+2))/s *
        (x : ℂ)^s/(s+lemma84SmoothingBeta D μ)^2) 0 (5*lemma44PaperAlpha D) =
      lemma84MainTerm D c j μ x := by
  have hb := lemma84_smoothing_beta_norm μ hα
  have hn : lemma84SmoothingBeta D μ ≠ 0 := norm_pos_iff.mp hb.1
  have hm : ‖lemma84SmoothingBeta D μ‖ < 5*lemma44PaperAlpha D := by linarith only [hb.2,hα]
  simp only [lemma84_positive_cpow_eq_exp hx]
  have hh := lemma84_model_circle_integral (lemma83PaperBeta D c (j+1))
    (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ) (Real.log x : ℂ) hn hm
  simpa only [lemma84MainTerm,lemma84_positive_cpow_eq_exp hx] using hh

end ZhangLS.Spec
