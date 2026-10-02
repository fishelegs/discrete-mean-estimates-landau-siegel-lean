import ZhangLS.Spec.Lemma61ReciprocalTailKernel
import ZhangLS.Spec.Lemma153NormalizationNonzero
import ZhangLS.Spec.PaperErrorScaleBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Actual paper P₄ and β-shift phases in15.16/4382, retaining the true scale.
No identification with the full r₁* r₁ⱼ residue products is assumed. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

lemma lemma153_exp_imaginary_difference (x y : ℝ) :
    ‖Complex.exp (I*(x:ℂ))-Complex.exp (I*(y:ℂ))‖≤|x-y| := by
  have he : Complex.exp (I*(x:ℂ))-Complex.exp (I*(y:ℂ)) =
      Complex.exp (I*(y:ℂ))*(Complex.exp (I*((x-y:ℝ):ℂ))-1) := by
    rw [mul_sub,mul_one,←Complex.exp_add]
    push_cast
    congr 2
    ring
  rw [he,norm_mul,Complex.norm_exp]
  simp only [mul_re,I_re,I_im,ofReal_re,ofReal_im,zero_mul,one_mul,sub_zero,Real.exp_zero,one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

lemma lemma153_P4_log_difference {D : ℕ} (hL : 3≤lemma23PaperL D) :
    Real.log (lemma61PaperP4 D)-Real.log (lemma23PaperP D)=
      519*Real.log (lemma23PaperL D)-2*Real.log (lemma56PaperT D) := by
  rw [lemma61_P4_PT0_log_identity hL]
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have ht : 0<lemma51PaperT0 D := pow_pos (by linarith : 0<lemma23PaperL D) 519
  rw [Real.log_mul hP.ne' ht.ne',lemma51PaperT0,Real.log_pow]
  ring

lemma lemma153_P4_log_difference_bound {D : ℕ} (hL : 3≤lemma23PaperL D) :
    |Real.log (lemma61PaperP4 D)-Real.log (lemma23PaperP D)|≤
      521*Real.log (lemma56PaperT D) := by
  have hL0 : 0<lemma23PaperL D := by linarith
  have hLt : lemma23PaperL D≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤lemma23PaperL D)
      (by norm_num : (1:ℝ)≤11/10)
  have hlog : 0≤Real.log (lemma23PaperL D) := Real.log_nonneg (by linarith)
  have hlog' : Real.log (lemma23PaperL D)≤Real.log (lemma56PaperT D) :=
    (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have ht : 0≤Real.log (lemma56PaperT D) := by linarith only [hLt,hL0]
  rw [lemma153_P4_log_difference hL]
  calc
    _ ≤ |519*Real.log (lemma23PaperL D)|+|2*Real.log (lemma56PaperT D)| := abs_sub _ _
    _ = 519*Real.log (lemma23PaperL D)+2*Real.log (lemma56PaperT D) := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    _ ≤ _ := by linarith only [hlog']

lemma lemma153_alpha_logP {D : ℕ} (hL : 0<lemma23PaperL D) :
    lemma44PaperAlpha D*Real.log (lemma23PaperP D)=Real.pi := by
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  field_simp

noncomputable def lemma153PhaseErrorConstant (c : ℝ) : ℝ := 5*Real.pi*c+1563

lemma lemma153_offset_P4_phase_error {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) :
    |lemma23PaperOffsetOne D c*Real.log (lemma61PaperP4 D)-Real.pi|≤
      lemma153PhaseErrorConstant c*lemma44PaperAlpha D*Real.log (lemma56PaperT D) ∧
    |lemma23PaperOffsetTwo D c*Real.log (lemma61PaperP4 D)-2*Real.pi|≤
      lemma153PhaseErrorConstant c*lemma44PaperAlpha D*Real.log (lemma56PaperT D) := by
  let α := lemma44PaperAlpha D
  let L := lemma23PaperL D
  let t := Real.log (lemma56PaperT D)
  let δ := c*α*L
  let θ := Real.log (lemma61PaperP4 D)-Real.log (lemma23PaperP D)
  have hα : 0<α := (lemma44_alpha_pos_le_one hL).1
  have hL0 : 0<L := by dsimp [L]; linarith
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hLt : L≤t := by
    dsimp [L,t]
    rw [lemma56PaperT,Real.log_exp]
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤lemma23PaperL D)
      (by norm_num : (1:ℝ)≤11/10)
  have ht : 0≤t := by linarith
  have hlogP := lemma153_alpha_logP hL0
  have hoff := lemma52_offset_bounds hL hc hsmall
  have hθ : |θ|≤521*t := lemma153_P4_log_difference_bound hL
  have hδbound : δ≤c*α*t := mul_le_mul_of_nonneg_left hLt (by positivity)
  have he1 : lemma23PaperOffsetOne D c*Real.log (lemma61PaperP4 D)-Real.pi =
      -5*Real.pi*δ+lemma23PaperOffsetOne D c*θ := by
    dsimp [δ,θ,lemma23PaperOffsetOne]
    dsimp [α,L] at *
    linear_combination -5*c*lemma44PaperAlpha D*lemma23PaperL D*hlogP + hlogP
  have he2 : lemma23PaperOffsetTwo D c*Real.log (lemma61PaperP4 D)-2*Real.pi =
      2*Real.pi*δ+lemma23PaperOffsetTwo D c*θ := by
    dsimp [δ,θ,lemma23PaperOffsetTwo]
    dsimp [α,L] at *
    linear_combination 2*c*lemma44PaperAlpha D*lemma23PaperL D*hlogP + 2*hlogP
  have hcommon (b : ℝ) (hb : 0≤b) (hb' : b≤3*α) : |b*θ|≤1563*α*t := by
    rw [abs_mul,abs_of_nonneg hb]
    calc
      _ ≤ (3*α)*(521*t) := by gcongr
      _ = _ := by ring
  constructor
  · rw [he1]
    calc
      _ ≤ |-5*Real.pi*δ|+|lemma23PaperOffsetOne D c*θ| := abs_add_le _ _
      _ ≤ 5*Real.pi*(c*α*t)+1563*α*t := by
        apply add_le_add _ (hcommon _ hoff.1.1 hoff.1.2)
        rw [show -5*Real.pi*δ=-(5*Real.pi*δ) by ring,abs_neg,abs_of_nonneg (by positivity)]
        gcongr
      _ = _ := by unfold lemma153PhaseErrorConstant; dsimp [α,t]; ring
  · rw [he2]
    calc
      _ ≤ |2*Real.pi*δ|+|lemma23PaperOffsetTwo D c*θ| := abs_add_le _ _
      _ ≤ 2*Real.pi*(c*α*t)+1563*α*t := by
        apply add_le_add _ (hcommon _ hoff.2.1.1 hoff.2.1.2)
        rw [abs_of_nonneg (by positivity)]
        gcongr
      _ ≤ _ := by unfold lemma153PhaseErrorConstant; dsimp [α,t] at *; nlinarith only [mul_nonneg (mul_nonneg Real.pi_pos.le hc.le) (mul_nonneg hα.le ht)]

lemma lemma153_beta_gap_one (D : ℕ) (c : ℝ) :
    lemma52PaperBetaThree D c-lemma52PaperBetaOne D c=lemma52PaperBetaTwo D c := by
  linear_combination -(lemma52_beta_sum D c)
lemma lemma153_beta_gap_two (D : ℕ) (c : ℝ) :
    lemma52PaperBetaThree D c-lemma52PaperBetaTwo D c=lemma52PaperBetaOne D c := by
  linear_combination -(lemma52_beta_sum D c)

lemma lemma153_P4_cpow_imaginary {D : ℕ} (hL : 3≤lemma23PaperL D) (x : ℝ) :
    (lemma61PaperP4 D:ℂ)^(I*(x:ℂ))=
      Complex.exp (I*((x*Real.log (lemma61PaperP4 D):ℝ):ℂ)) := by
  have hpos : 0<lemma61PaperP4 D := by
    unfold lemma61PaperP4 lemma51PaperT0 lemma23PaperP lemma56PaperT
    have : 0<Real.log (D:ℝ) := by change 0<lemma23PaperL D; linarith
    positivity
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),←Complex.ofReal_log hpos.le]
  congr 1
  push_cast
  ring

noncomputable def lemma153PhaseSign (j : Fin 3) : ℂ :=
  if j=1 then -1 else 1

lemma lemma153_actual_P4_phase_bound {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖(lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma83PaperBeta D c j)-
        lemma153PhaseSign j‖≤
      lemma153PhaseErrorConstant c*lemma44PaperAlpha D*Real.log (lemma56PaperT D) := by
  have hphase := lemma153_offset_P4_phase_error hL hc hsmall
  have he1 : Complex.exp (I*(Real.pi:ℂ))=-1 := by
    simpa [mul_comm] using Complex.exp_pi_mul_I
  have he2 : Complex.exp (I*((2*Real.pi:ℝ):ℂ))=1 := by
    convert Complex.exp_two_pi_mul_I using 1; push_cast; congr 1; ring
  fin_cases j
  · change ‖(lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma52PaperBetaOne D c)-1‖≤_
    rw [lemma153_beta_gap_one,lemma52PaperBetaTwo,lemma153_P4_cpow_imaginary hL,←he2]
    exact (lemma153_exp_imaginary_difference _ _).trans hphase.2
  · change ‖(lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma52PaperBetaTwo D c)-(-1)‖≤_
    rw [lemma153_beta_gap_two,lemma52PaperBetaOne,lemma153_P4_cpow_imaginary hL,←he1]
    exact (lemma153_exp_imaginary_difference _ _).trans hphase.1
  · change ‖(lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma52PaperBetaThree D c)-1‖≤_
    simp only [sub_self,Complex.cpow_zero,norm_zero]
    have ha := (lemma44_alpha_pos_le_one hL).1
    have ht : 0≤Real.log (lemma56PaperT D) := by
      rw [lemma56PaperT,Real.log_exp]
      exact Real.rpow_nonneg (by linarith) _
    unfold lemma153PhaseErrorConstant
    positivity

end ZhangLS.Spec
