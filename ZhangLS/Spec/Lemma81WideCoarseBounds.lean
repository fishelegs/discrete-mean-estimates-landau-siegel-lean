import ZhangLS.Spec.Lemma81ReplacementLittleO

/-! # Coarse actual L and inverse-Z bounds for the remaining contour edges

The wider strip reaches J(1). Exponential-in-L^9 bounds are sufficient because
the original Gaussian on the horizontal boundary decays as exp(-c L^10).
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real
set_option maxHeartbeats 2000000

def Lemma81WideStrip (D : ℕ) (s : ℂ) : Prop :=
  1/2-lemma44PaperAlpha D ≤ s.re ∧ s.re ≤ 3/2 ∧
    |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1

lemma lemma81_wide_strip_parameters {D : ℕ} (hL : 3 ≤ lemma23PaperL D) {s : ℂ}
    (hs : Lemma81WideStrip D s) :
    1/4 ≤ s.re ∧ |s.re-1/2| ≤ 1 ∧ |s.re| ≤ 2*lemma23PaperL D^9 ∧
      |s.im-(lemma23PaperCenter D).im| ≤ 2*lemma23PaperL D^405+3 := by
  have ha := lemma51_alpha_le_quarter hL
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hp : 1 ≤ lemma23PaperL D^9 := one_le_pow₀ hL1
  have hsr : 1/4 ≤ s.re := by linarith only [ha,hs.1]
  refine ⟨hsr,abs_le.mpr ⟨by linarith only [hsr],by linarith only [hs.2.1]⟩,?_,?_⟩
  · rw [abs_of_nonneg (by linarith only [hsr] : 0 ≤ s.re)]
    linarith only [hs.2.1,hp]
  · linarith only [hs.2.2,pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 405]

lemma lemma81_actual_L_coarse_exponential {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 100 ≤ lemma23PaperL D) {s : ℂ} (hσ : 1/4 ≤ s.re) (hσhi : s.re ≤ 2)
    (ht : |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+2) :
    ‖ψ.LFunction s‖ ≤ Real.exp (100*lemma23PaperL D^9) := by
  have hL3 : 3 ≤ lemma23PaperL D := by linarith only [hL]
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hT1 : 1 ≤ lemma51PaperT0 D := one_le_pow₀ hL1
  have hT : 0 < lemma51PaperT0 D := pow_pos hLp 519
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hσp : 0 < s.re := by linarith only [hσ]
  have him := lemma59_large_height_bound hL (by linarith only [ht] :
    |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+20)
  have hn : ‖s‖ ≤ 12*lemma51PaperT0 D := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hσp.le] at hh
    change |s.im| ≤ 10*lemma51PaperT0 D at him
    linarith only [hh,hσhi,him,hT1]
  have hp := lemma59_family_modulus_le_two_P ψ hL hψ
  have hquot : (p : ℝ)/s.re ≤ 4*(p : ℝ) := by
    apply (div_le_iff₀ hσp).mpr
    nlinarith only [hσ,(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hbound : ‖ψ.LFunction s‖ ≤ 96*(lemma23PaperP D*lemma51PaperT0 D) := by
    calc
      _ ≤ ‖s‖*((p : ℝ)/s.re) := lemma56_actual_LFunction_bound_re_pos ψ
        (lemma59_family_character_nonprincipal ψ hψ) hσp
      _ ≤ (12*lemma51PaperT0 D)*(4*(p : ℝ)) := mul_le_mul hn hquot (by positivity) (by positivity)
      _ ≤ (12*lemma51PaperT0 D)*(8*lemma23PaperP D) :=
        mul_le_mul_of_nonneg_left (by linarith only [hp]) (by positivity)
      _ = _ := by ring
  have hPT : lemma23PaperP D*lemma51PaperT0 D ≤ Real.exp (2*lemma23PaperL D^9) := by
    rw [← Real.exp_log (mul_pos hP hT)]
    exact Real.exp_le_exp.mpr (lemma61_PT0_log_bounds hL3).2
  have h96 : (96 : ℝ) ≤ Real.exp 96 := by linarith only [Real.add_one_le_exp (96 : ℝ)]
  have hp9 : 1 ≤ lemma23PaperL D^9 := one_le_pow₀ hL1
  calc
    _ ≤ 96*(lemma23PaperP D*lemma51PaperT0 D) := hbound
    _ ≤ Real.exp 96*Real.exp (2*lemma23PaperL D^9) :=
      mul_le_mul h96 hPT (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (96+2*lemma23PaperL D^9) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hp9])

lemma lemma81_inverse_Z_coarse_exponential {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma81WideStrip D s) :
    ‖(lemma23DirichletZ ψ s)⁻¹‖ ≤ Real.exp (37*lemma23PaperL D^9) := by
  have hp := lemma81_wide_strip_parameters hL hs
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hlog := lemma61_family_Z_log_modulus_wide ψ hψ hL hp.2.2.1 hp.2.2.2
  have ht : 0 < s.im := by linarith only [(lemma61_wide_height_data hL hp.2.2.2).2.1]
  have hn : 0 < ‖lemma23DirichletZ ψ s‖ := norm_pos_iff.mpr
    (lemma23DirichletZ_ne_zero_of_im_pos ψ hψ.2.1 hψ.1.ne_one ht)
  have hPT := lemma61_PT0_log_bounds hL
  have hterm : Real.log (lemma23PaperP D*lemma51PaperT0 D)*(s.re-1/2) ≤
      2*lemma23PaperL D^9 := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hp.2.1).2 hPT.1
    linarith only [hh,hPT.2]
  have hinv : lemma23PaperL D^(-68 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ hL1 (by norm_num)
  have herr : 35*lemma23PaperL D^(-68 : ℤ)*|s.re-1/2| ≤ 35 := by
    have hh := mul_le_mul hinv hp.2.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hh]
  have h9 : 1 ≤ lemma23PaperL D^9 := one_le_pow₀ hL1
  have hexp : -Real.log ‖lemma23DirichletZ ψ s‖ ≤ 37*lemma23PaperL D^9 := by
    have hh := (abs_le.mp hlog).1
    linarith only [hh,hterm,herr,h9]
  rw [norm_inv,← Real.exp_log hn,← Real.exp_neg]
  exact Real.exp_le_exp.mpr hexp

end ZhangLS.Spec
