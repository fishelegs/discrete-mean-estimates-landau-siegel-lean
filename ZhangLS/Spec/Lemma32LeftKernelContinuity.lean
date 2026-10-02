import ZhangLS.Spec.Lemma32ActualTailReduction
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32LeftLine (t : ℝ) : ℂ := ((-1/4 : ℝ) : ℂ)+(t : ℂ)*I
noncomputable def lemma32LeftKernel (t : ℝ) : ℝ :=
  ‖riemannZeta (1+lemma32LeftLine t)‖^8*‖1+lemma32LeftLine t‖^8*
    ‖Complex.Gamma (lemma32LeftLine t)‖

lemma lemma32_left_line_Gamma_continuous : Continuous (fun t : ℝ => Complex.Gamma (lemma32LeftLine t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hg : DifferentiableAt ℂ Complex.Gamma (lemma32LeftLine t) :=
    Complex.differentiableAt_Gamma _ (by
      intro m hm
      have hr := congrArg Complex.re hm
      simp only [lemma32LeftLine,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,
        zero_mul,sub_zero,add_zero,neg_re,natCast_re] at hr
      cases m with
      | zero => norm_num at hr
      | succ m =>
        have hn : (1 : ℝ) ≤ (m+1 : ℕ) := by exact_mod_cast Nat.succ_pos m
        linarith)
  exact hg.continuousAt.comp' (f := lemma32LeftLine) (by unfold lemma32LeftLine;fun_prop)

lemma lemma32_left_line_zeta_continuous : Continuous (fun t : ℝ => riemannZeta (1+lemma32LeftLine t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn : 1+lemma32LeftLine t ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [lemma32LeftLine,mul_re] at hr
  exact (differentiableAt_riemannZeta hn).continuousAt.comp'
    (f := fun t : ℝ => 1+lemma32LeftLine t) (by unfold lemma32LeftLine;fun_prop)

lemma lemma32_left_kernel_continuous : Continuous lemma32LeftKernel := by
  unfold lemma32LeftKernel
  exact ((lemma32_left_line_zeta_continuous.norm.pow 8).mul
    ((show Continuous (fun t : ℝ => 1+lemma32LeftLine t) from by
      unfold lemma32LeftLine;fun_prop).norm.pow 8)).mul lemma32_left_line_Gamma_continuous.norm

lemma lemma32_left_kernel_nonneg (t : ℝ) : 0 ≤ lemma32LeftKernel t := by
  unfold lemma32LeftKernel
  positivity

end ZhangLS.Spec
