import ZhangLS.Spec.Lemma153ActualPhase
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

noncomputable def lemma153ShiftRatio (D : ℕ) (c : ℝ) (j : Fin 3) : ℂ :=
  lemma52PaperBetaOne D c*lemma52PaperBetaTwo D c /
    ((lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j)*
      (lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j))

lemma lemma153_actual_beta_factorization (D : ℕ) (c : ℝ) :
    lemma52PaperBetaOne D c = I*(lemma44PaperAlpha D:ℂ)*(1-5*((c*lemma44PaperAlpha D*lemma23PaperL D:ℝ):ℂ)) ∧
    lemma52PaperBetaTwo D c = I*(lemma44PaperAlpha D:ℂ)*(2*(1+((c*lemma44PaperAlpha D*lemma23PaperL D:ℝ):ℂ))) ∧
    lemma52PaperBetaThree D c = I*(lemma44PaperAlpha D:ℂ)*(3*(1-((c*lemma44PaperAlpha D*lemma23PaperL D:ℝ):ℂ))) := by
  unfold lemma52PaperBetaOne lemma52PaperBetaTwo lemma52PaperBetaThree
    lemma23PaperOffsetOne lemma23PaperOffsetTwo lemma23PaperOffsetThree
  push_cast
  constructor
  · ring
  constructor <;> ring

lemma lemma153_actual_shift_ratio_formula {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    lemma153ShiftRatio D c j =
      if j=0 then (((1-5*(c*lemma44PaperAlpha D*lemma23PaperL D))/(1+7*(c*lemma44PaperAlpha D*lemma23PaperL D)):ℝ):ℂ)
      else if j=1 then ((-(2*(1+c*lemma44PaperAlpha D*lemma23PaperL D))/(1+7*(c*lemma44PaperAlpha D*lemma23PaperL D)):ℝ):ℂ)
      else 1 := by
  let δ := c*lemma44PaperAlpha D*lemma23PaperL D
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hδ0 : 0≤δ := by
    dsimp [δ]
    have : 0<lemma23PaperL D := by linarith
    positivity
  have hδ1 : δ≤1/10 := hsmall
  have h1 : (1:ℂ)-5*(δ:ℂ)≠0 := by
    have : 0<1-5*δ := by linarith
    exact_mod_cast this.ne'
  have h2 : (1:ℂ)+(δ:ℂ)≠0 := by
    have : 0<1+δ := by linarith
    exact_mod_cast this.ne'
  have h7 : (1:ℂ)+7*(δ:ℂ)≠0 := by
    have : 0<1+7*δ := by linarith
    exact_mod_cast this.ne'
  have ha' : (lemma44PaperAlpha D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hf := lemma153_actual_beta_factorization D c
  have hb1 : lemma52PaperBetaOne D c≠0 := by rw [hf.1]; exact mul_ne_zero (mul_ne_zero I_ne_zero ha') h1
  have hb2 : lemma52PaperBetaTwo D c≠0 := by rw [hf.2.1]; exact mul_ne_zero (mul_ne_zero I_ne_zero ha') (mul_ne_zero (by norm_num) h2)
  have hgap : lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c =
      I*(lemma44PaperAlpha D:ℂ)*(1+7*(δ:ℂ)) := by rw [hf.1,hf.2.1]; dsimp [δ]; ring
  have hgn : lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c≠0 := by rw [hgap]; exact mul_ne_zero (mul_ne_zero I_ne_zero ha') h7
  fin_cases j
  · change lemma52PaperBetaOne D c*lemma52PaperBetaTwo D c /
      ((lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c)*(lemma52PaperBetaThree D c-lemma52PaperBetaOne D c)) =
      (((1-5*δ)/(1+7*δ):ℝ):ℂ)
    rw [lemma153_beta_gap_one]
    have he : lemma52PaperBetaOne D c*lemma52PaperBetaTwo D c/
      ((lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c)*lemma52PaperBetaTwo D c)=
      lemma52PaperBetaOne D c/(lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c) := by field_simp
    rw [he,hgap,hf.1]
    change I*(lemma44PaperAlpha D:ℂ)*(1-5*(δ:ℂ))/(I*(lemma44PaperAlpha D:ℂ)*(1+7*(δ:ℂ)))=_
    push_cast
    field_simp
  · change lemma52PaperBetaOne D c*lemma52PaperBetaTwo D c /
      ((lemma52PaperBetaThree D c-lemma52PaperBetaTwo D c)*(lemma52PaperBetaOne D c-lemma52PaperBetaTwo D c)) =
      ((-(2*(1+δ))/(1+7*δ):ℝ):ℂ)
    rw [lemma153_beta_gap_two]
    rw [show lemma52PaperBetaOne D c-lemma52PaperBetaTwo D c=-(lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c) by ring]
    rw [hgap,hf.1,hf.2.1]
    change (I*(lemma44PaperAlpha D:ℂ)*(1-5*(δ:ℂ)))*(I*(lemma44PaperAlpha D:ℂ)*(2*(1+(δ:ℂ))))/
      ((I*(lemma44PaperAlpha D:ℂ)*(1-5*(δ:ℂ)))*(-(I*(lemma44PaperAlpha D:ℂ)*(1+7*(δ:ℂ)))))=_
    push_cast
    field_simp
  · change lemma52PaperBetaOne D c*lemma52PaperBetaTwo D c /
      ((lemma52PaperBetaOne D c-lemma52PaperBetaThree D c)*(lemma52PaperBetaTwo D c-lemma52PaperBetaThree D c))=1
    rw [show lemma52PaperBetaOne D c-lemma52PaperBetaThree D c=-(lemma52PaperBetaThree D c-lemma52PaperBetaOne D c) by ring,
      show lemma52PaperBetaTwo D c-lemma52PaperBetaThree D c=-(lemma52PaperBetaThree D c-lemma52PaperBetaTwo D c) by ring,
      lemma153_beta_gap_one,lemma153_beta_gap_two]
    field_simp

noncomputable def lemma153LeadingWeight (j : Fin 3) : ℂ := if j=1 then 2 else 1
noncomputable def lemma153LeadingSignedWeight (j : Fin 3) : ℂ := if j=1 then -2 else 1

lemma lemma153_real_ratio_bounds {δ : ℝ} (hδ : 0≤δ) (hsmall : δ≤1/10) :
    |(1-5*δ)/(1+7*δ)|≤2 ∧ |(1-5*δ)/(1+7*δ)-1|≤12*δ ∧
    |-(2*(1+δ))/(1+7*δ)|≤2 ∧ |-(2*(1+δ))/(1+7*δ)-(-2)|≤12*δ := by
  have hd : 0<1+7*δ := by linarith
  have hd1 : 1≤1+7*δ := by linarith
  have ha0 : 0≤(1-5*δ)/(1+7*δ) := div_nonneg (by linarith) hd.le
  have ha1 : (1-5*δ)/(1+7*δ)≤1 := (div_le_one hd).mpr (by linarith)
  have hb0 : -(2*(1+δ))/(1+7*δ)≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  have hb2 : -2≤-(2*(1+δ))/(1+7*δ) := (le_div_iff₀ hd).mpr (by linarith)
  have he1 : (1-5*δ)/(1+7*δ)-1=-(12*δ/(1+7*δ)) := by field_simp; ring
  have he2 : -(2*(1+δ))/(1+7*δ)-(-2)=12*δ/(1+7*δ) := by field_simp; ring
  have herr : |12*δ/(1+7*δ)|≤12*δ := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self (by positivity) hd1
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_of_nonneg ha0]; linarith
  · rw [he1,abs_neg]; exact herr
  · rw [abs_of_nonpos hb0]; linarith
  · rw [he2]; exact herr

lemma lemma153_actual_shift_ratio_bounds {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖lemma153ShiftRatio D c j‖≤2 ∧
    ‖lemma153ShiftRatio D c j-lemma153LeadingSignedWeight j‖≤
      12*c*lemma44PaperAlpha D*lemma23PaperL D := by
  let δ := c*lemma44PaperAlpha D*lemma23PaperL D
  have hδ : 0≤δ := by
    dsimp [δ]
    have := (lemma44_alpha_pos_le_one hL).1
    have : 0≤lemma23PaperL D := by linarith
    positivity
  have hb := lemma153_real_ratio_bounds hδ hsmall
  rw [lemma153_actual_shift_ratio_formula hL hc hsmall]
  fin_cases j
  · change ‖(((1-5*δ)/(1+7*δ):ℝ):ℂ)‖≤2 ∧
      ‖(((1-5*δ)/(1+7*δ):ℝ):ℂ)-1‖≤12*c*lemma44PaperAlpha D*lemma23PaperL D
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    exact ⟨hb.1,by convert hb.2.1 using 1; dsimp [δ]; ring⟩
  · change ‖((-(2*(1+δ))/(1+7*δ):ℝ):ℂ)‖≤2 ∧
      ‖((-(2*(1+δ))/(1+7*δ):ℝ):ℂ)-(-2)‖≤12*c*lemma44PaperAlpha D*lemma23PaperL D
    have he : (((-(2*(1+δ))/(1+7*δ):ℝ):ℂ)-(-2))=
      (((-(2*(1+δ))/(1+7*δ)-(-2):ℝ)):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    exact ⟨hb.2.2.1,by convert hb.2.2.2 using 1; dsimp [δ]; ring⟩
  · change ‖(1:ℂ)‖≤2 ∧ ‖(1:ℂ)-1‖≤12*c*lemma44PaperAlpha D*lemma23PaperL D
    simp only [norm_one,sub_self,norm_zero]
    exact ⟨by norm_num,by convert mul_nonneg (by norm_num : (0:ℝ)≤12) hδ using 1; dsimp [δ]; ring⟩

end ZhangLS.Spec
