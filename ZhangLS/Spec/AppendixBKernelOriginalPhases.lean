import ZhangLS.Spec.AppendixBKernelPhaseComparison

/-! The genuine finite-D shifts converge to the printed full-kernel constants,
with quantified logarithmic and T corrections, uniformly in l1<T. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex Filter

lemma appendixB_alpha_logP {D : ℕ} (hL : 0<lemma23PaperL D) :
    lemma44PaperAlpha D*lemma23PaperL D^9=Real.pi := by
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  exact div_mul_cancel₀ _ (pow_ne_zero _ hL.ne')

lemma appendixB_original_frequency_bounds (μ : Fin 3) :
    1≤appendixBOriginalFrequency μ ∧ appendixBOriginalFrequency μ≤3 ∧
      1/4≤appendixBOriginalExponent μ ∧
      0≤appendixBOriginalTCost μ ∧ appendixBOriginalTCost μ≤10 := by
  fin_cases μ <;> norm_num [appendixBOriginalFrequency,appendixBOriginalExponent,appendixBOriginalTCost]

lemma appendixB_original_gamma_eq (D : ℕ) (μ : Fin 3) :
    appendixBOriginalGamma D μ=I*((appendixBOriginalFrequency μ*lemma44PaperAlpha D : ℝ) : ℂ) := by
  fin_cases μ <;> norm_num [appendixBOriginalGamma,appendixBOriginalFrequency,lemma151Beta6,lemma151Beta7] <;> ring

lemma appendixB_original_gamma_lower {D : ℕ} (μ : Fin 3)
    (hα : 0<lemma44PaperAlpha D) :
    lemma44PaperAlpha D≤‖appendixBOriginalGamma D μ‖ := by
  rw [appendixB_original_gamma_eq,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (mul_pos (by have := (appendixB_original_frequency_bounds μ).1; linarith) hα)]
  nlinarith only [(appendixB_original_frequency_bounds μ).1,hα]

lemma appendixB_original_beta_perturbation {D : ℕ} {c : ℝ}
    (hc : 0<c) (hL : 0<lemma23PaperL D) (j : Fin 3) :
    ‖lemma83PaperBeta D c j-I*((j.val+1 : ℕ) : ℂ)*(lemma44PaperAlpha D : ℂ)‖≤
      5*c*lemma44PaperAlpha D^2*lemma23PaperL D := by
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity [Real.pi_pos]
  fin_cases j
  all_goals norm_num only [lemma83PaperBeta,Fin.mk.injEq,ite_true,ite_false,lemma52PaperBetaOne,
    lemma52PaperBetaTwo,lemma52PaperBetaThree,lemma23PaperOffsetOne,lemma23PaperOffsetTwo,
    lemma23PaperOffsetThree,Nat.cast_add,Nat.cast_one,Nat.cast_zero,Nat.cast_ofNat]
  all_goals push_cast
  · have he : I * ((lemma44PaperAlpha D : ℂ) * (1-5*(c : ℂ)*lemma44PaperAlpha D*lemma23PaperL D))-
        I*1*(lemma44PaperAlpha D : ℂ)=
        I*((-5*c*lemma44PaperAlpha D^2*lemma23PaperL D : ℝ) : ℂ) := by push_cast; ring
    rw [he,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonpos (by nlinarith only [mul_nonneg (mul_nonneg (by positivity : 0≤5*c) (sq_nonneg (lemma44PaperAlpha D))) hL.le])]
    ring_nf
    exact le_rfl
  · have he : I * (2*(lemma44PaperAlpha D : ℂ) * (1+(c : ℂ)*lemma44PaperAlpha D*lemma23PaperL D))-
        I*2*(lemma44PaperAlpha D : ℂ)=
        I*((2*c*lemma44PaperAlpha D^2*lemma23PaperL D : ℝ) : ℂ) := by push_cast; ring
    rw [he,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    nlinarith only [mul_nonneg (mul_nonneg hc.le (sq_nonneg (lemma44PaperAlpha D))) hL.le]
  · have he : I * (3*(lemma44PaperAlpha D : ℂ) * (1-(c : ℂ)*lemma44PaperAlpha D*lemma23PaperL D))-
        I*3*(lemma44PaperAlpha D : ℂ)=
        I*((-3*c*lemma44PaperAlpha D^2*lemma23PaperL D : ℝ) : ℂ) := by push_cast; ring
    rw [he,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonpos (by nlinarith only [mul_nonneg (mul_nonneg (by positivity : 0≤3*c) (sq_nonneg (lemma44PaperAlpha D))) hL.le])]
    nlinarith only [mul_nonneg (mul_nonneg hc.le (sq_nonneg (lemma44PaperAlpha D))) hL.le]

lemma appendixB_log_model_at_printed (α S r a : ℝ) (j : ℕ)
    (hα : 0<α) (hS : 0<S) (hr : 0<r) (ha : 0<a) (hid : α*S=Real.pi) :
    appendixBLogModel (r*S) 0 (I*(j : ℂ)*(α : ℂ)) (I*((a*α : ℝ) : ℂ))=
      lemma151FullKernelConstant r a j := by
  have he : (I*((a*α : ℝ) : ℂ))*((r*S : ℝ) : ℂ)=((a*r*Real.pi : ℝ) : ℂ)*I := by
    rw [←hid]
    push_cast
    ring
  have hαC : (α : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hα.ne'
  have haC : (a : ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hrC : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hSC : (S : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hidC : (α : ℂ)*(S : ℂ)=(Real.pi : ℂ) := by exact_mod_cast hid
  have hB : (I*(j : ℂ)*(α : ℂ))/(I*((a*α : ℝ) : ℂ))^2/((r*S : ℝ) : ℂ)=
      (j : ℂ)/((a : ℂ)^2*r*Real.pi*I) := by
    rw [←hidC]
    push_cast
    field_simp
    <;> ring
  have hA : (I*(j : ℂ)*(α : ℂ))/(I*((a*α : ℝ) : ℂ))=(j : ℂ)/(a : ℂ) := by
    push_cast
    field_simp
  unfold appendixBLogModel lemma151FullKernelConstant
  simp only [sub_zero,zero_div,Complex.ofReal_zero,sub_zero,mul_one]
  rw [he,hA,hB]
  ring

lemma appendixB_original_phase_budget {D : ℕ} (c : ℝ) (hL : 0<lemma23PaperL D) :
    appendixBPhaseBudget (lemma44PaperAlpha D) (lemma23PaperL D^9/4)
      (5*c*lemma44PaperAlpha D^2*lemma23PaperL D) (Real.log (lemma56PaperT D))=
      ((5*Real.pi+40)*c*lemma23PaperL D+
        (412+960/Real.pi+132*Real.pi)*Real.log (lemma56PaperT D))/lemma23PaperL D^9 := by
  have hα : lemma44PaperAlpha D=Real.pi/lemma23PaperL D^9 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
  rw [hα]
  unfold appendixBPhaseBudget
  field_simp [hL.ne',Real.pi_ne_zero]
  <;> ring

noncomputable def appendixBOriginalError (D : ℕ) (c : ℝ) : ℝ :=
  (4*(appendixBContourBudget D+275*Real.exp (5*Real.pi))+
    (5*Real.pi+40)*c*lemma23PaperL D+
    (412+960/Real.pi+132*Real.pi)*Real.log (lemma56PaperT D))/lemma23PaperL D^9

/-- The printed e2 and e3 constants, and e1-prime for the full P1 kernel,
with every finite-D and cutoff correction explicitly bounded. -/
theorem appendixB_original_printed_constants_uniform {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ j μ : Fin 3, ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBFullKernelSum (appendixBOriginalCutoff D μ) (lemma83PaperBeta D c j)
          (appendixBOriginalGamma D μ) l₁-
        lemma151FullKernelConstant (appendixBOriginalExponent μ) (appendixBOriginalFrequency μ)
          (j.val+1)‖≤appendixBOriginalError D c := by
  obtain ⟨N,hN,hfull⟩ := appendixB_original_full_kernels_uniform hc
  obtain ⟨M,hM,hsmall⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨K,hK⟩ := eventually_atTop.mp appendixB_original_cutoffs_eventually
  refine ⟨max N (max M K),hN.trans (le_max_left _ _),?_⟩
  intro D hD j μ l₁ hl hlT
  obtain ⟨hL,hfullD⟩ := hfull D ((le_max_left _ _).trans hD)
  have hMK : max M K≤D := (le_max_right _ _).trans hD
  obtain ⟨hL1,hcuts⟩ := hK D ((le_max_right _ _).trans hMK)
  obtain ⟨hX,hXT,hXP,hlog⟩ := hcuts μ
  have hLp : 0<lemma23PaperL D := by linarith only [hL]
  have hS : 0<lemma23PaperL D^9 := pow_pos hLp 9
  have hα := (lemma83_alpha_small (by linarith only [hL] : 100≤lemma23PaperL D)).1
  have hbounds := appendixB_original_frequency_bounds μ
  have ha : 0<appendixBOriginalFrequency μ := by linarith only [hbounds.1]
  have hr : 0<appendixBOriginalExponent μ := by linarith only [hbounds.2.2.1]
  have hT : 0≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    exact Real.rpow_nonneg hLp.le _
  have hlLog := appendixB_original_log_l1 hl hlT
  have hlogT : Real.log (l₁ : ℝ)≤Real.log (lemma56PaperT D) :=
    (Real.log_lt_log (Nat.cast_pos.mpr hl) hlT).le
  have hb := lemma83_paper_beta_norm (by linarith only [hL] : 3≤lemma23PaperL D)
    hc (hsmall D ((le_max_left _ _).trans hMK)) j
  have hb₀ : ‖I*((j.val+1 : ℕ) : ℂ)*(lemma44PaperAlpha D : ℂ)‖≤3*lemma44PaperAlpha D := by
    rw [norm_mul,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hα,
      Complex.norm_natCast]
    have hj : ((j.val+1 : ℕ) : ℝ)≤3 := by exact_mod_cast (by omega : j.val+1≤3)
    exact mul_le_mul_of_nonneg_right hj hα.le
  have hdu : |Real.log (appendixBOriginalCutoff D μ)-
      appendixBOriginalExponent μ*lemma23PaperL D^9|≤10*Real.log (lemma56PaperT D) := by
    rw [appendixB_original_cutoff_log]
    have he : appendixBOriginalExponent μ*lemma23PaperL D^9-
      appendixBOriginalTCost μ*Real.log (lemma56PaperT D)-
      appendixBOriginalExponent μ*lemma23PaperL D^9=
      -(appendixBOriginalTCost μ*Real.log (lemma56PaperT D)) := by ring
    rw [he,abs_neg,abs_of_nonneg (mul_nonneg hbounds.2.2.2.1 hT)]
    exact mul_le_mul_of_nonneg_right hbounds.2.2.2.2 hT
  have hmodel := appendixB_log_model_stability hα (by positivity : 0<lemma23PaperL D^9/4)
    (by positivity : 0≤5*c*lemma44PaperAlpha D^2*lemma23PaperL D) hT
    (appendixB_original_gamma D μ hα).1 (appendixB_original_gamma_lower μ hα)
    (appendixB_original_gamma D μ hα).2.2 hb hb₀
    (appendixB_original_beta_perturbation hc hLp j)
    (by linarith only [hlog] : lemma23PaperL D^9/4≤Real.log (appendixBOriginalCutoff D μ))
    (by nlinarith only [hbounds.2.2.1,hS] : lemma23PaperL D^9/4≤appendixBOriginalExponent μ*lemma23PaperL D^9)
    hlLog.1 hlogT hdu
  rw [appendixB_original_gamma_eq] at hmodel
  rw [appendixB_log_model_at_printed _ _ _ _ _ hα hS hr ha (appendixB_alpha_logP hLp)] at hmodel
  rw [←appendixB_original_gamma_eq] at hmodel
  rw [←appendixB_model_as_log_model (by linarith only [hX]) (Real.log_pos hX).ne' _ _ hl,
    appendixB_original_phase_budget c hLp] at hmodel
  have hh := norm_add_le
    (appendixBFullKernelSum (appendixBOriginalCutoff D μ) (lemma83PaperBeta D c j)
      (appendixBOriginalGamma D μ) l₁-
      appendixBModelLeading (appendixBOriginalCutoff D μ) (appendixBOriginalCutoff D μ/l₁)
        (lemma83PaperBeta D c j) (appendixBOriginalGamma D μ))
    (appendixBModelLeading (appendixBOriginalCutoff D μ) (appendixBOriginalCutoff D μ/l₁)
        (lemma83PaperBeta D c j) (appendixBOriginalGamma D μ)-
      lemma151FullKernelConstant (appendixBOriginalExponent μ) (appendixBOriginalFrequency μ) (j.val+1))
  rw [sub_add_sub_cancel] at hh
  exact hh.trans ((add_le_add (hfullD j μ l₁ hl hlT) hmodel).trans_eq (by
    unfold appendixBOriginalError
    rw [←add_div]
    congr 1
    ring))

end ZhangLS.Spec
