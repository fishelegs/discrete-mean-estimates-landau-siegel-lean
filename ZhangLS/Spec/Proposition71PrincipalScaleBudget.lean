import ZhangLS.Spec.Proposition71ZetaAuxiliaryHeight
import ZhangLS.Spec.Proposition71ZetaPaperStrip
import ZhangLS.Spec.Lemma56
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

lemma proposition71_principal_scale_right {D : ℕ} (hL : 0<lemma23PaperL D)
    {q : ℝ} (hq : 0<q) (hqhi : q≤lemma23PaperP D^10) :
    q^(1+lemma44PaperAlpha D)≤q*Real.exp (10*Real.pi) := by
  have hlog : Real.log q≤10*lemma23PaperL D^9 := by
    have hh := Real.log_le_log hq hqhi
    simpa only [Real.log_pow,lemma23PaperP,Real.log_exp,Nat.cast_ofNat] using hh
  have hα : lemma44PaperAlpha D=Real.pi/lemma23PaperL D^9 := by
    simp [lemma44PaperAlpha,lemma23PaperP]
  have hα₀ : 0≤lemma44PaperAlpha D := by rw [hα]; positivity
  have hb : Real.log q*lemma44PaperAlpha D≤10*Real.pi := by
    apply (mul_le_mul_of_nonneg_right hlog hα₀).trans_eq
    rw [hα]
    field_simp
  have he : q^(1+lemma44PaperAlpha D)=q*Real.exp (Real.log q*lemma44PaperAlpha D) := by
    rw [Real.rpow_def_of_pos hq,show Real.log q*(1+lemma44PaperAlpha D)=
      Real.log q+Real.log q*lemma44PaperAlpha D by ring,Real.exp_add,Real.exp_log hq]
  rw [he]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) hq.le

lemma proposition71_principal_scale_left {D : ℕ} (hL : 0<lemma23PaperL D)
    {q : ℝ} (hq : 0<q) (hqlo : lemma56PaperT D^2≤q) :
    q^(1-1/lemma23PaperL D)*proposition71ZetaAuxHeight D≤
      q*Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  have hT : 0<(lemma56PaperT D)^2 := sq_pos_of_pos (lemma56_paper_T_pos D)
  have hlog : 2*lemma23PaperL D^(11/10 : ℝ)≤Real.log q := by
    have hh := Real.log_le_log hT hqlo
    simpa only [Real.log_pow,lemma56PaperT,Real.log_exp,Nat.cast_ofNat] using hh
  have hex : lemma23PaperL D^(11/10 : ℝ)/lemma23PaperL D=lemma23PaperL D^(1/10 : ℝ) := by
    rw [show (11/10 : ℝ)=(1/10 : ℝ)+1 by norm_num,Real.rpow_add hL,
      Real.rpow_one,mul_div_cancel_right₀ _ hL.ne']
  have hb : 2*lemma23PaperL D^(1/10 : ℝ)≤Real.log q/lemma23PaperL D := by
    simpa only [mul_div_assoc,hex] using div_le_div_of_nonneg_right hlog hL.le
  have he : q^(1-1/lemma23PaperL D)*proposition71ZetaAuxHeight D=
      q*Real.exp (-Real.log q/lemma23PaperL D+lemma23PaperL D^(1/10 : ℝ)) := by
    rw [Real.rpow_def_of_pos hq,proposition71ZetaAuxHeight,←Real.exp_add]
    have hexp : Real.log q*(1-1/lemma23PaperL D)+(Real.log (D : ℝ))^(1/10 : ℝ)=
        Real.log q+(-Real.log q/lemma23PaperL D+lemma23PaperL D^(1/10 : ℝ)) := by
      change Real.log q*(1-1/lemma23PaperL D)+lemma23PaperL D^(1/10 : ℝ)=_
      ring
    rw [hexp,Real.exp_add,Real.exp_log hq]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hq.le
  apply Real.exp_le_exp.mpr
  simp only [neg_div]
  linarith

end ZhangLS.Spec
