import ZhangLS.Spec.AppendixBTailGaussianMellin
import ZhangLS.Spec.AppendixBKernelOriginalUniform

/-! Original source scales throughout z in [.5,.504], uniformly for positive
l1<T. In particular the source contour uses the actual log(l1) shift. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Filter Set

lemma appendixB_source_scale_log (D : ℕ) (z : ℝ) {l₁ : ℕ} (hl : 0<l₁) :
    Real.log (Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ))=
      z*lemma23PaperL D^9-Real.log (l₁ : ℝ) := by
  rw [Real.log_div (Real.exp_pos _).ne' (Nat.cast_pos.mpr hl).ne',Real.log_exp]

/-- One threshold precedes every real z in the original integration interval
and every positive l1<T. No tail estimate is assumed to obtain this geometry. -/
theorem appendixB_source_scales_uniform :
    ∀ᶠ D : ℕ in atTop, 1<lemma23PaperL D ∧
      ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ∀ z : ℝ, z∈Icc (0.5 : ℝ) 0.504 →
      lemma56PaperT D<Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ) ∧
      Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ)<lemma23PaperP D ∧
      lemma44PaperAlpha D*Real.log (Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ))≤Real.pi := by
  filter_upwards [appendixB_original_cutoffs_eventually] with D hD
  have hL := hD.1
  have hLp : 0<lemma23PaperL D := by linarith
  have hS : 0<lemma23PaperL D^9 := by positivity
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hP3 : lemma56PaperT D^2<lemma151P3 D := by
    simpa [appendixBOriginalCutoff] using (hD.2 (2 : Fin 3)).2.1
  have hP3exp : lemma151P3 D=Real.exp (0.498*lemma23PaperL D^9) := by
    rw [lemma151P3,Real.rpow_def_of_pos hP,lemma23PaperP,Real.log_exp]
    congr 1
    ring
  rw [hP3exp] at hP3
  refine ⟨hL,?_⟩
  intro l₁ hl hlT z hz
  have hlr : 0<(l₁ : ℝ) := Nat.cast_pos.mpr hl
  have hx : 0<Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ) :=
    div_pos (Real.exp_pos _) hlr
  have hxT : lemma56PaperT D<Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ) := by
    apply (lt_div_iff₀ hlr).mpr
    have hlmul := mul_lt_mul_of_pos_left hlT (lemma56_paper_T_pos D)
    have hexp : Real.exp (0.498*lemma23PaperL D^9)≤Real.exp (z*lemma23PaperL D^9) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hz.1]
    have hTprod : lemma56PaperT D*lemma56PaperT D<Real.exp (0.498*lemma23PaperL D^9) := by
      simpa [pow_two] using hP3
    exact hlmul.trans (hTprod.trans_le hexp)
  have hxP : Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ)<lemma23PaperP D := by
    apply (div_le_self (Real.exp_pos _).le (by exact_mod_cast hl)).trans_lt
    unfold lemma23PaperP
    apply Real.exp_lt_exp.mpr
    nlinarith [hz.2]
  exact ⟨hxT,hxP,lemma84_alpha_log_x_le_pi hLp hx hxP⟩

end ZhangLS.Spec
