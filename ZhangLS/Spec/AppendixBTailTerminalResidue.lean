import ZhangLS.Spec.AppendixBTailResidueRate

/-! The integrated actual finite-D residue and its terminal small-phase
constant. This is a residue calculation, not a sharp arithmetic tail theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex MeasureTheory

noncomputable def appendixBIntegratedExactTailResidue (D : ℕ) (β γ : ℂ) : ℂ :=
  (1/0.504 : ℂ)*(∫ z : ℝ in (0.5 : ℝ)..0.504,
    lemma151ExactTailResidue D (lemma23PaperL D^9) z β γ)

lemma appendixB_actual_beta_ne_zero {D : ℕ} {c : ℝ}
    (hc : 0<c) (hL : 0<lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    lemma83PaperBeta D c j≠0 := by
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity [Real.pi_pos]
  have hd := appendixB_original_beta_perturbation hc hL j
  have hj : 1≤((j.val+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1≤j.val+1)
  have hn : lemma44PaperAlpha D≤‖I*((j.val+1 : ℕ) : ℂ)*(lemma44PaperAlpha D : ℂ)‖ := by
    rw [norm_mul,norm_mul,norm_I,one_mul,Complex.norm_natCast,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hα]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤5*lemma44PaperAlpha D by positivity)
  intro he
  rw [he,zero_sub,norm_neg] at hd
  nlinarith

lemma appendixB_original_tail_leading_phase {D : ℕ}
    (hL : 0<lemma23PaperL D) (j : ℕ) (z : ℝ) :
    ((I*(j : ℂ)*(lemma44PaperAlpha D : ℂ))/(lemma151Beta6 D))*
      lemma151TailNumerator (lemma23PaperL D^9) z (lemma151Beta6 D) 0=
      ((j : ℂ)/(3/2 : ℂ))*
        (exp (((3/2 : ℝ)*(0.504-z)*Real.pi : ℝ)*I)-
          exp ((0.006*Real.pi : ℝ)*I)) := by
  have hα : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity [Real.pi_pos]
  have hid := appendixB_alpha_logP hL
  have hidC : (lemma44PaperAlpha D : ℂ)*(lemma23PaperL D^9 : ℝ)=Real.pi := by
    exact_mod_cast hid
  have hquot : (I*(j : ℂ)*(lemma44PaperAlpha D : ℂ))/(lemma151Beta6 D)=
      (j : ℂ)/(3/2 : ℂ) := by
    unfold lemma151Beta6
    field_simp [Complex.ofReal_ne_zero.mpr hα.ne']
    <;> ring
  rw [hquot]
  congr 1
  unfold lemma151TailNumerator lemma151Beta6
  simp only [mul_zero,add_zero]
  apply congrArg₂ (fun a b : ℂ => exp a-exp b)
  all_goals rw [←hid]; push_cast; ring

lemma appendixB_integrated_original_leading_tail {D : ℕ}
    (hL : 0<lemma23PaperL D) (j : ℕ) :
    (1/0.504 : ℂ)*(∫ z : ℝ in (0.5 : ℝ)..0.504,
      ((I*(j : ℂ)*(lemma44PaperAlpha D : ℂ))/(lemma151Beta6 D))*
        lemma151TailNumerator (lemma23PaperL D^9) z (lemma151Beta6 D) 0)=
      lemma151ResidueTail j := by
  simp_rw [appendixB_original_tail_leading_phase hL j]
  rw [intervalIntegral.integral_const_mul]
  unfold lemma151ResidueTail
  ring

/-- The terminal residue constant has a proved finite-D correction.
This preserves c-prime and yields an explicit O_c(L^-8) rate without alpha1. -/
theorem appendixB_integrated_exact_tail_rate {D : ℕ} {c : ℝ}
    (hL : 100≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖appendixBIntegratedExactTailResidue D (lemma83PaperBeta D c j) (lemma151Beta6 D)-
      lemma151ResidueTail (j.val+1)‖≤
      (10*c*Real.pi*lemma23PaperL D/lemma23PaperL D^9+
        240*Real.pi/lemma23PaperL D^9)/126 := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hα := lemma83_alpha_small hL
  have hβ := appendixB_actual_beta_ne_zero hc hLp hsmall j
  have hβn := lemma83_paper_beta_norm (by linarith) hc hsmall j
  have hg := appendixB_original_gamma D (0 : Fin 3) hα.1
  have hγre : (lemma151Beta6 D).re=0 := by simpa [appendixBOriginalGamma] using hg.1
  have hγhi : ‖lemma151Beta6 D‖≤3*lemma44PaperAlpha D := by simpa [appendixBOriginalGamma] using hg.2.2
  have hγlo : lemma44PaperAlpha D≤‖lemma151Beta6 D‖ := by
    change lemma44PaperAlpha D≤‖appendixBOriginalGamma D (0 : Fin 3)‖
    exact appendixB_original_gamma_lower (0 : Fin 3) hα.1
  let E := 10*c*Real.pi*lemma23PaperL D/lemma23PaperL D^9+240*Real.pi/lemma23PaperL D^9
  let f := fun z : ℝ => lemma151ExactTailResidue D (lemma23PaperL D^9) z
    (lemma83PaperBeta D c j) (lemma151Beta6 D)
  let g := fun z : ℝ => ((I*((j.val+1 : ℕ) : ℂ)*(lemma44PaperAlpha D : ℂ))/(lemma151Beta6 D))*
    lemma151TailNumerator (lemma23PaperL D^9) z (lemma151Beta6 D) 0
  have hb (z : ℝ) : ‖f z-g z‖≤E := by
    have hl := appendixB_tail_residue_local_error (by linarith) hα.1 hα.2
      (lemma23PaperL D^9) z hβ hβn hγre hγlo hγhi
    have hm := appendixB_actual_tail_beta_rate hc hLp j z
    have ht := norm_add_le
      (f z-((lemma83PaperBeta D c j)/(lemma151Beta6 D))*
        lemma151TailNumerator (lemma23PaperL D^9) z (lemma151Beta6 D) 0)
      (((lemma83PaperBeta D c j)/(lemma151Beta6 D))*
        lemma151TailNumerator (lemma23PaperL D^9) z (lemma151Beta6 D) 0-g z)
    rw [sub_add_sub_cancel] at ht
    apply ht.trans ((add_le_add hl hm).trans_eq ?_)
    dsimp [E]
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    ring
  have hf : Continuous f := by
    dsimp [f,lemma151ExactTailResidue,lemma151TailNumerator]
    fun_prop
  have hgc : Continuous g := by
    dsimp [g,lemma151TailNumerator]
    fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0.5 : ℝ))
    (b := (0.504 : ℝ)) (f := fun z => f z-g z) (C := E) (fun z _ => hb z)
  rw [←appendixB_integrated_original_leading_tail hLp (j.val+1)]
  unfold appendixBIntegratedExactTailResidue
  change ‖(1/0.504 : ℂ)*(∫ z in (0.5 : ℝ)..0.504, f z)-
    (1/0.504 : ℂ)*(∫ z in (0.5 : ℝ)..0.504, g z)‖≤_
  rw [←mul_sub,←intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hgc.intervalIntegrable _ _),norm_mul]
  norm_num at hi ⊢
  have hh := mul_le_mul_of_nonneg_left hi (show 0≤(125/63 : ℝ) by norm_num)
  exact hh.trans_eq (by dsimp [E]; ring)

/-- Only the final change of variable uses [0,.004]; the exact source residue
above has always used z in [.5,.504]. -/
theorem appendixB_integrated_tail_bstar_rate {D : ℕ} {c : ℝ}
    (hL : 100≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖appendixBIntegratedExactTailResidue D (lemma83PaperBeta D c j) (lemma151Beta6 D)-
      (-I*Real.pi*(j.val+1)*lemma151BStar)‖≤
      (10*c*Real.pi*lemma23PaperL D/lemma23PaperL D^9+
        240*Real.pi/lemma23PaperL D^9)/126 := by
  simpa only [lemma151_residue_tail_eq_neg_pi_I_bstar,Nat.cast_add,Nat.cast_one] using
    appendixB_integrated_exact_tail_rate hL hc hsmall j

end ZhangLS.Spec
