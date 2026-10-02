import ZhangLS.Spec.Lemma102TentBridge
import ZhangLS.Spec.Lemma101Ranges
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

lemma lemma102_initial_main_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0<d) (hr : 0<r) :
    (500/(Real.log (lemma23PaperP D):ℂ))*
      (LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j (lemma101Cutoff D (d*r:ℝ) (63/125))-
       2*(LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j (lemma101Cutoff D (d*r:ℝ) (251/500)))+
       LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j (lemma101Cutoff D (d*r:ℝ) (1/2))) =
      lemma102MainInitial χ c j d r := by
  have hy : (0:ℝ)<d*r := by positivity
  have hp : Real.log (lemma23PaperP D)≠0 := (Real.log_pos (lemma101_P_gt_one hD)).ne'
  have hp' : (Real.log (lemma23PaperP D):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp
  unfold lemma102LogMain lemma102MainInitial
  simp only [lemma101_log_cutoff hy]
  push_cast
  field_simp <;> ring

lemma lemma102_lower_main_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0<d) (hr : 0<r) :
    (500/(Real.log (lemma23PaperP D):ℂ))*
      (LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j (lemma101Cutoff D (d*r:ℝ) (63/125))-
       2*(LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j (lemma101Cutoff D (d*r:ℝ) (251/500)))) =
      lemma102MainLower χ c j d r := by
  have hy : (0:ℝ)<d*r := by positivity
  have hp : 0< lemma23PaperP D^(1/2:ℝ) := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hlog (a : ℝ) : Real.log (lemma23PaperP D^a/(d*r:ℝ))=
      a*Real.log (lemma23PaperP D)-Real.log (d*r:ℝ) := lemma101_log_cutoff hy a
  have hpow : Real.log (lemma23PaperP D^(1/2:ℝ))=(1/2)*Real.log (lemma23PaperP D) :=
    Real.log_rpow (Real.exp_pos _) _
  unfold lemma102LogMain lemma102MainLower lemma102Y1 lemma101Cutoff
  simp only [hlog,Real.log_div hy.ne' hp.ne',hpow]
  push_cast
  ring

lemma lemma102_upper_main_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) :
    (500/(Real.log (lemma23PaperP D):ℂ))*
      (LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j (lemma101Cutoff D (d*r:ℝ) (63/125))) =
      lemma102MainUpper χ c j d r := by
  unfold lemma102LogMain lemma102MainUpper lemma102Y2 lemma101Cutoff
  ring

lemma lemma102_second_difference_norm (x₁ x₂ x₃ y₁ y₂ y₃ : ℂ) {E : ℝ}
    (h₁ : ‖x₁-y₁‖≤E) (h₂ : ‖x₂-y₂‖≤E) (h₃ : ‖x₃-y₃‖≤E) :
    ‖(x₁-2*x₂+x₃)-(y₁-2*y₂+y₃)‖≤4*E := by
  rw [show (x₁-2*x₂+x₃)-(y₁-2*y₂+y₃)=(x₁-y₁)-2*(x₂-y₂)+(x₃-y₃) by ring]
  have h := (norm_add_le ((x₁-y₁)-2*(x₂-y₂)) (x₃-y₃)).trans
    (add_le_add (norm_sub_le (x₁-y₁) (2*(x₂-y₂))) le_rfl)
  simp only [norm_mul,Complex.norm_ofNat] at h
  linarith

lemma lemma102_two_term_norm (x₁ x₂ y₁ y₂ : ℂ) {E : ℝ} (hE : 0≤E)
    (h₁ : ‖x₁-y₁‖≤E) (h₂ : ‖x₂-y₂‖≤E) :
    ‖(x₁-2*x₂)-(y₁-2*y₂)‖≤4*E := by
  simpa using lemma102_second_difference_norm x₁ x₂ 0 y₁ y₂ 0 h₁ h₂ (by simpa using hE)

lemma lemma102_scale_error {D : ℕ} (hL : 0<lemma23PaperL D)
    (z : ℂ) {E : ℝ} (hE : ‖z‖≤E*lemma23PaperL D^(-6:ℤ)) :
    ‖(500/(Real.log (lemma23PaperP D):ℂ))*z‖≤500*E*lemma23PaperL D^(-15:ℤ) := by
  rw [norm_mul,lemma101_prefactor_norm hL]
  apply (mul_le_mul_of_nonneg_left hE (by positivity)).trans_eq
  simp only [zpow_neg,zpow_ofNat]
  field_simp <;> ring

end ZhangLS.Spec
